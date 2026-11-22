import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0760
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0761
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0769
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0762
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0766
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0771
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

theorem GlobalTheory.AscFin.psiE_superdiag_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr i j hij v hv o ho
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hsh : shiftId G ≠ 0 := mul_ne_zero hm (inv_ne_zero hmB)
  have h1 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (inv_ne_zero hAA) v
    (GlobalTheory.T.inv_AA_multiple_depth_lattice_maps_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have h2 := GlobalTheory.T.besselJacobi_superdiagonal_entries_at_place D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hsh)) v
    (GlobalTheory.T.besselStep_depthLattice_mulVec_mem_completion D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have e1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc * (D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI
    rw [inv_inv]
    ring
  have e2 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc *
      ((D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹ * (shiftId G)⁻¹)⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI shiftId
    rw [mul_inv, inv_inv, inv_inv]
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hx := GlobalTheory.T.mem_completion_of_mem_modulus_and_conj_quotients G.pl sc v _ _ h1 h2
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hψ := ((GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v).2.2.2.2.1 _ hxA).1 hx o ho
  have ho' : GlobalTheory.FinPlLoc.idem D (· = v) * o = o := (GlobalTheory.FinPlLoc.mem_idAt_iff _ o).1 ho.1
  rw [← ho']
  rw [← hψ]
  congr 1
  ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  first | exact @GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | exact GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | (intros; apply GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000

namespace GlobalTheory.LineZero

variable {D : D7}

noncomputable def mulL {k m n : ℕ} (A : Mx D k m) : Mx D m n →+ Mx D k n where
  toFun y := A * y
  map_zero' := Matrix.mul_zero _
  map_add' y y' := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S B T : HSp D} (M : Matrix (Fin T.rank) (Fin B.rank) D.host.E)
    {LS : Set (Fin S.rank → D.host.E)} {LB : Set (Fin B.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hM : ∀ t ∈ LB, M *ᵥ t ∈ LT) {y : WO S B} (hy : y ∈ latO S B LS LB P) :
    (rat M : Mx D T.rank B.rank) * y ∈ latO S T LS LT P := by
  suffices h : latO S B LS LB P ≤ (latO S T LS LT P).comap (mulL (rat M : Mx D T.rank B.rank)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

end GlobalTheory.LineZero

namespace GlobalTheory.LineZero

variable {D : D7}

theorem latO_le_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib,
      TensorProduct.tmul_neg, neg_neg]
  rw [e]
  exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩)

theorem rat_mul_mem_hatMx {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E)
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} {N' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)}
    (hA : ∀ x ∈ N, A * x ∈ N') {y : Mx D m n} (hy : y ∈ hatMx N) : (rat A : Mx D k m) * y ∈ hatMx N' := by
  suffices h : hatMx N ≤ (hatMx N').comap (mulL (rat A : Mx D k m)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, A * x, hA x hx, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.tmul_sum]

theorem mul_mem_smul_homLat {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') (I : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ I • homLat Λ Λ') : A * x ∈ I • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun _ _ hy hy' => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hy z hz)
  · rw [Matrix.mul_add]
    exact add_mem hy hy'

end GlobalTheory.LineZero

open GlobalTheory.LineZero in

theorem GlobalTheory.LineZero.adj_mem_lineLat : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF h u hu
  have h1 := GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO D hq T L μ0 hL sc G W M hM F hF h u hu
  have h2 := GlobalTheory.T.star_adjoint_mem_hat_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  have hz : ∀ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0}, F.oz.iB *ᵥ t ∈ G.Λ (.core 0) := by
    intro t ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [Matrix.mulVec_smul, hF.zB]
    refine Submodule.smul_mem _ c ?_
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, zero_mem _, fun _ => 1, fun _ => FractionalIdeal.one_mem_one _, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  show _ ∈ (latCore G 0).comap _
  rw [AddSubgroup.mem_comap]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    AddMonoidHom.inr_apply]
  rw [GlobalTheory.MixModel.OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB * _)]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_le_negSp (rat_mul_mem_latO F.oz.iB hz h1)
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx F.oz.iB (fun x hx => mul_mem_smul_homLat F.oz.iB hz _ hx) (h2 e he)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTowerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower : FockTot → PartFixed → RungJ := by
  first | exact @GlobalTheory.Asc.RungJac.rungJ | exact GlobalTheory.Asc.RungJac.rungJ | (intros; apply GlobalTheory.Asc.RungJac.rungJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.BottomLevel

theorem fin_vec_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, h₁, hU₁⟩ := GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom hX t
  obtain ⟨U₂, h₂, hU₂⟩ := GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector hX t
  exact ⟨U₁ ⊓ U₂, h₁.inter h₂, fun κ hκ hf => hU₂ κ hκ.2 hf (hU₁ κ hκ.1 hf)⟩

theorem rightTranslate_level : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (J : Subgroup (GA D WW)) (M₂ : IntermediateField ℚ ℂ), IsOpen (J : Set (GA D WW)) ∧ FiniteDimensional ℚ M₂ ∧
      ∀ t, ∀ κ ∈ J, κ ∈ GfC WW → ∃ ℓ ∈ M₂, ∀ P x, X.I W.ψ W.θ t P (x * κ) = ℓ * X.I W.ψ W.θ t P x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hf : ∀ t, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) := fun t =>
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hX.is.fst t) hX.is.isVac.2.theta
  choose U hUo hU using fin_vec_fix hX
  refine ⟨⨅ t, U t, ⊥, ?_, inferInstance, fun t κ hκ hκf => ⟨1, one_mem _, fun P x => ?_⟩⟩
  · rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite fun t => hUo t
  · have hfix := hU t κ (Subgroup.mem_iInf.1 hκ t) hκf
    have hW := hX.is.weil t
    have hpt := GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW W.θ hθ 1 (one_mem _) κ hκf
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (hf t)
    have e1 : ∀ g, (X.ω t).toSgn true (1, κ) g = X.ω t (1, κ) g := by
      intro g; simp [GlobalTheory.Grid.WRep.toSgn]
    rw [one_mul]
    unfold Tri.I Tri.ker thetaKO
    congr 1
    funext g
    have hm : ((g, x * κ) : GA D A × GA D WW) = (g, x) * (1, κ) := by simp
    rw [hm, map_mul, Module.End.mul_apply, ← e1, hpt, e1, hfix]
end GlobalTheory.BottomLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixPair

theorem om_pow_eq {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ))
    (g : GA D S × GA D V) (f : WO S V → ℂ) (c : ℂ) (hc : om g f = c • f) : ∀ m : ℕ, om (g ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

set_option maxHeartbeats 1000000 in

theorem pair_fix_vacO : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hvac hsdS hsdT hcS hcT hW
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, ∀ x' ∈ GfC T, GlobalTheory.Member.FinCong S n.factorial x →
      GlobalTheory.Member.FinCong T n.factorial x' →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x x' u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' u hu hu' using hne
    have ht : Filter.Tendsto (fun n => ((k n, k' n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).prodMk_nhds
        (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk' hkc')
    obtain ⟨n, hn⟩ := (ht.eventually hev).exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S n₁.factorial k →
      GlobalTheory.Member.FinCong T n₁.factorial k' → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') v = c • v := by
    intro k hk k' hk' hc hc'
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T k k' u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ k'⁻¹ u, hn₁ k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk')
          (GlobalTheory.Member.PrincLevel.finCong_inv hc) (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
        rw [inv_inv, inv_inv] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk k' hk' hc hc' u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ
      sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk' τ, Matrix.one_mul, Matrix.mul_one]) hΛ v hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T)
      sS sT (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT
      hsdS hsdT v _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun p : GA D S × GA D T => om p v w₀ := hW.om_cont _ hvac.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k →
      GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k' → om (k, k') v = v := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, k' n ^ m) v = c • v ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (by rw [← Prod.pow_mk]; exact om_pow_eq om _ v c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht : Filter.Tendsto (fun n => ((k n ^ m n, k' n ^ m n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)).prodMk_nhds
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2))
    have e1 : om (1 : GA D S × GA D T) v w₀ = v w₀ := by
      rw [map_one]
      rfl
    have h2 : Filter.Tendsto (fun n => om (k n ^ m n, k' n ^ m n) v w₀) Filter.atTop (𝓝 (v w₀)) := by
      have := (hcont.tendsto 1).comp ht
      rw [← e1]
      exact this
    have hpos : 0 < ‖v w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (v w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨n₁.factorial * n.factorial, Nat.mul_pos n₁.factorial_pos n.factorial_pos,
    fun k hk k' hk' hc hc' => hn k hk k' hk' hc hc'⟩

end GlobalTheory.VacFixPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeFirstRowEqDoubleAnnihilatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeFirstRow_eq_doubleAnnihilator : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  first | exact @GlobalTheory.AscFin.LatticeBidual.latRow_bidual | exact GlobalTheory.AscFin.LatticeBidual.latRow_bidual | (intros; apply GlobalTheory.AscFin.LatticeBidual.latRow_bidual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_moveV_eq | exact GlobalTheory.RowVertexInv.sum_prod_moveV_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_moveV_eq <;> assumption)
end

