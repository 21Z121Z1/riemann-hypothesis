import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataCm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_torusExtension | exact GlobalTheory.SS.potModel_semiAbelian_torusExtension | (intros; apply GlobalTheory.SS.potModel_semiAbelian_torusExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.AmplePull

theorem ampleAt_pull : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
    AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  intro Y X π _ N hN x h
  obtain ⟨m, A, s, hm, hA, hAmp, hy⟩ := h
  have hNm : (lbPow N m).IsLB := isLB_lbPow hN m
  have hP : (LB.div (lbPow N m) A).IsLB := LB.isLB_div hNm hA
  have hN' : (N.pull π).IsLB := LB.isLB_pull hN π
  have hA' : (A.pull π).IsLB := LB.isLB_pull hA π
  have hNm' : (lbPow (N.pull π) m).IsLB := isLB_lbPow hN' m
  have hQ : (LB.div (lbPow (N.pull π) m) (A.pull π)).IsLB := LB.isLB_div hNm' hA'
  have iso : LBIso (LB.div (lbPow (N.pull π) m) (A.pull π)) ((LB.div (lbPow N m) A).pull π) := by
    rw [← cls_eq_iff hQ (LB.isLB_pull hP π), cls_div hNm' hA' hQ, cls_pull hP π, cls_div hNm hA hP,
      cls_lbPow hN' m hNm', cls_pull hN π hN', cls_pull hA π hA', cls_lbPow hN m hNm, map_sub, map_nsmul]
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ (LB.isLB_pull hP π) iso (ZM.RepBC.secPull _ π s)
  refine ⟨m, A.pull π, t, hm, hA', hAmp.pull_of_isAffineHom π, ?_⟩
  rw [ht, GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
  exact hy

end GlobalTheory.AmplePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_branching_constant_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.main | exact GlobalTheory.InfSize.main | (intros; apply GlobalTheory.InfSize.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DifferentAtBasePlace

theorem ne_of_mod_eq_one' {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

theorem natAbs_discr_F_dvd (D : D7) : (discr D.host.F).natAbs ∣ (discr D.host.E).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.F (𝓞 D.host.F) D.host.E (𝓞 D.host.E)]
  exact Dvd.dvd.mul_left (dvd_pow_self _ Module.finrank_pos.ne') _

theorem leastSplitAuxiliaryPrime_not_dvd_discr_base (D : D7) : ¬ q0 D ∣ (discr D.host.F).natAbs := by
  obtain ⟨hp, hm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  intro h
  have hc : q0 D ∣ Formalism.BasicNotions.LevelStarExponents.condE D :=
    D.host.der.discr_primes.1 _ hp (Int.natCast_dvd.2 (h.trans (natAbs_discr_F_dvd D)))
  exact ne_of_mod_eq_one' hm (dvd_mul_of_dvd_right hc _) hp.one_lt rfl

theorem not_dvd_different {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) :
    ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro h
  have hdisc : ((discr D.host.F : ℤ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal :=
    Ideal.le_of_dvd h (discr_mem_differentIdeal D.host.F (𝓞 D.host.F))
  have hq : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal := G.pl.basePlace_over_qZero
  have hcop : IsCoprime (q0 D : ℤ) (discr D.host.F) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (leastSplitAuxiliaryPrimeThetaChain_spec D).1).2 (leastSplitAuxiliaryPrime_not_dvd_discr_base D))
  obtain ⟨u, v, huv⟩ := hcop
  apply G.pl.v0.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 D.host.F) huv
  push_cast at this
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hq)) (Ideal.mul_mem_left _ _ hdisc)

end GlobalTheory.DifferentAtBasePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem ratHyp0_at_point : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  intro eps Fm x hx i p hp hM t ht hlow j
  obtain ⟨hc, -, hu, -⟩ := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hTie : TieIn p.T p.R.toRealDat p.κ p.v₀ :=
    ⟨p.fw.laws, p.fw.alg_eq, p.fw.kap, p.fw.hv₀, p.fw.chiR, p.fw.x0⟩
  exact
    { size := (Fm.parT x hx i).nV_ge
      host := p.host
      std := GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)
      laws := p.fw.laws
      core :=
        { lev := hc.lev
          grp := ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩
          fam := ⟨hc.fam.tie, hc.fam.Sb, hc.fam.roots, hc.fam.pl_onto, hc.fam.degR, hc.fam.degL, hc.fam.muVal, hc.fam.etaVal⟩
          models := ⟨hc.models.inf, hc.models.vpos, hc.models.cX, hc.models.cV, hc.models.prX, hc.models.HX, hc.models.HV,
            hc.models.HE, hc.models.HW, hc.models.gE, hc.models.gW, hc.models.jX, hc.models.jV, hc.models.νY, hc.models.νY',
            hc.models.ν0, hc.models.νX, hc.models.νV, hc.models.νW, hc.models.BV, hc.models.order⟩
          chain := ⟨hc.chain.ωY, hc.chain.ωX, hc.chain.vY, hc.chain.vX, hc.chain.ptY, hc.chain.ptX, hc.chain.ItY, hc.chain.ItX,
            hc.chain.ioY, hc.chain.ioX, hc.chain.Th⟩
          thP := ⟨hc.thP.ωP, hc.thP.vP, hc.thP.pt_theta, hc.thP.ioP, hc.thP.thF_mem, hc.thP.thF, hc.thP.thG⟩ }
      unif := hu
      fw := ⟨p.fw⟩
      tieIn := hTie
      io := hp.ioExt
      guard := p.qGuard
      fin := GlobalTheory.BigOn.Check.finite_tuples_of_indefiniteSidePoint p
      pins := p.pins j
      phase := p.phase j hu
      galois := (Fm.ties x i).baseField_isGalois
      small := hM.2.2.small
      inUse := ht
      low := hlow }

end GlobalTheory.BigOn.Exp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Adelic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionsFieldChange

open GlobalTheory.AbLaw
open scoped TensorProduct

variable {X Y : Scheme.{0}}

theorem ofSec_secPull {L : LB X} (s : L.Sec) (π : Y ⟶ X) (V : X.Opens) :
    GlobalTheory.LB.ofSec (secPull s π) (π ⁻¹ᵁ V) =
      SecOn.pullLE L π V (π ⁻¹ᵁ V) le_rfl (GlobalTheory.LB.ofSec s V) := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_ofSec, SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  exact GlobalTheory.LB.resG_appLE π _ _ (s.f (j PUnit.unit))

theorem ofSec_smul {L : LB X} (a : Γ(X, ⊤)) (s : L.Sec) (V : X.Opens) :
    GlobalTheory.LB.ofSec (a • s) V = rs X (le_top : V ≤ ⊤) a • GlobalTheory.LB.ofSec s V := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.smul_f, map_mul, GlobalTheory.resG_resG]
  exact congrArg (· * _) (GlobalTheory.resG_resG _ _ _).symm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev secModule {k : Type} [Field k] (S : LinSys k) : Module k S.L.Sec :=
  Module.compHom _ (algebraMap k Γ(S.Y, ⊤))

attribute [local instance] secModule

theorem secTower {k : Type} [Field k] (S : LinSys k) : IsScalarTower k Γ(S.Y, ⊤) S.L.Sec :=
  ⟨fun a g s => by
    show (algebraMap k Γ(S.Y, ⊤) a * g) • s = algebraMap k Γ(S.Y, ⊤) a • (g • s)
    rw [mul_smul]⟩

attribute [local instance] secTower

theorem isProper_str {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : IsProper S.str := by
  obtain ⟨N, i, hi, e⟩ := hS.proj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
  rw [← e]
  infer_instance

theorem finite_sec {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : Module.Finite k S.L.Sec := by
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) S.L) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj S.isLB
  exact Module.Finite.equiv ((cohZeroTwistEquiv S.L).restrictScalars k)

theorem finrank_baseChange (S : LinSys F) (hS : S.IsVariety) :
    Module.finrank E (S.baseChange E).L.Sec = Module.finrank F S.L.Sec := by
  have := isProper_str hS
  rw [← lineBundleGlobalSectionsDim_eq_finrank, ← lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_def, lineBundleGlobalSectionsDim_def]
  exact FieldChangeInter.hdim_pull (S.isPullback_baseChange E) S.isLB 0

def resTo {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens) :
    L.Sec →+ SecOnR f L V where
  toFun s := SecOnR.of f L V (GlobalTheory.LB.ofSec s V)
  map_zero' := SecOnR.ext fun i => by
    rw [SecOnR.coord_of, GlobalTheory.LB.coord_ofSec, LB.zero_f, map_zero, SecOnR.coord_zero]
  map_add' s t := SecOnR.ext fun i => by
    rw [SecOnR.coord_add, SecOnR.coord_of, SecOnR.coord_of, SecOnR.coord_of, GlobalTheory.LB.coord_ofSec,
      GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.add_f, map_add]

theorem resTo_smul {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens)
    (a : R) (s : L.Sec) :
    letI := algebraΓOfHom f
    resTo f L V (algebraMap R Γ(X, ⊤) a • s) = a • resTo f L V s :=
  ofSec_smul _ s V

theorem resTo_secPull (S : LinSys F) (E : Type) [Field E] [Algebra F E] (V : S.Y.Opens) (s : S.L.Sec) :
    resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ V) (secPull s (S.bcFst E)) =
      SecOnR.pull S.L (S.isPullback_baseChange E).w V _ le_rfl (resTo S.str S.L V s) :=
  congrArg (SecOnR.of _ _ _) (ofSec_secPull s (S.bcFst E) V)

def pullSecs (S : LinSys F) (E : Type) [Field E] [Algebra F E] {n : ℕ} (b : Fin n → S.L.Sec) :
    Fin n → (S.baseChange E).L.Sec := fun j => secPull (b j) (S.bcFst E)

theorem linearIndependent_secPull (S : LinSys F) (hS : S.IsVariety) {n : ℕ} (b : Fin n → S.L.Sec)
    (hb : LinearIndependent F b) :
    LinearIndependent E (pullSecs S E b) := by
  classical
  have := isProper_str hS
  haveI : CompactSpace S.Y := QuasiCompact.compactSpace_of_compactSpace S.str
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := S.Y) (V := ⊤) isCompact_univ
  have H := S.isPullback_baseChange E
  let R : (Fin n → F) →ₗ[F] (∀ i, SecOnR S.str S.L (D i)) :=
    LinearMap.pi fun i => ∑ j, (LinearMap.proj j).smulRight (resTo S.str S.L (D i) (b j))
  have hRi : ∀ u i, R u i = resTo S.str S.L (D i) (∑ j, u j • b j) := fun u i => by
    rw [map_sum]
    simp only [R, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => (resTo_smul S.str S.L (D i) (u j) (b j)).symm
  have hR : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun u hu => ?_
    have h2 : ∑ j, u j • b j = 0 := by
      refine (SecOn.ofSec_bijective (M := S.L) (V := ⊤) rfl).injective ?_
      refine SecOn.ext_of_cover D (fun _ => le_top) hc.ge fun a => ?_
      rw [SecOn.restrict_ofSec, SecOn.restrict_ofSec]
      have := (hRi u a).symm.trans (congrFun hu a)
      exact this.trans (map_zero (resTo S.str S.L (D a))).symm
    funext j
    exact Fintype.linearIndependent_iff.1 hb u h2 j
  let Bc : ∀ i, E ⊗[F] SecOnR S.str S.L (D i) →ₗ[E]
      SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) := fun i =>
    SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
  have hBc : ∀ i, Function.Bijective (Bc i) := fun i =>
    SecOnR.baseChangeHom_bijective S.isLB H (hD i) rfl
  let Φ : (Fin n → E) →ₗ[E] ∀ i, SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) :=
    LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).toLinearMap ∘ₗ
      R.baseChange E ∘ₗ (TensorProduct.piScalarRight F E E (Fin n)).symm.toLinearMap
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (R.baseChange E) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap R hR
    have h2 : Function.Injective (LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) :
        (∀ i, E ⊗[F] SecOnR S.str S.L (D i)) →ₗ[E] _) :=
      fun x y h => funext fun i => (hBc i).1 (congrFun h i)
    exact h2.comp ((TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).injective.comp
      (h1.comp (TensorProduct.piScalarRight F E E (Fin n)).symm.injective))
  have hΦc : ∀ c : Fin n → E, Φ c = fun i =>
      resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) (∑ j, c j • pullSecs S E b j) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    funext i
    rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single,
      LinearMap.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.pi_apply, LinearMap.proj_apply, Bc, SecOnR.baseChangeHom_tmul]
    change SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
      (c j ⊗ₜ[F] R (Pi.single j 1) i) = _
    rw [SecOnR.baseChangeHom_tmul, hRi]
    have hs : ∑ k, (Pi.single j (1 : F) : Fin n → F) k • b k = b j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    rw [hs, ← resTo_secPull]
    exact (resTo_smul _ _ _ (c j) _).symm
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h0 : Φ c = Φ 0 := by
    rw [hΦc, hc, map_zero]
    funext i
    exact map_zero _
  exact congrFun (hΦ h0)

theorem exists_pullSecs_spanning : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (S : LinSys F),
    S.IsVariety → ∃ (n : ℕ) (b : Fin n → S.L.Sec), ∀ t : (S.baseChange E).L.Sec, ∃ u : Fin n → E,
      (({ S with N := n, b := b } : LinSys F).baseChange E).comb u = t := by
  intro F E _ _ _ S hS
  haveI := finite_sec hS
  haveI : Module.Finite E (S.baseChange E).L.Sec := finite_sec (hS.baseChange E)
  let B := Module.finBasis F S.L.Sec
  refine ⟨_, B, fun t => ?_⟩
  have hli := linearIndependent_secPull (E := E) S hS B B.linearIndependent
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_baseChange S hS])
  have ht : t ∈ Submodule.span E (Set.range (pullSecs S E B)) := hsp ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ht
  exact ⟨u, hu⟩

end GlobalTheory.SectionsFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.BaseChangeVariety

theorem baseChange_props : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  intro k E _ _ _ Y X p q π D _ H hP _
  have hs : SmoothOfRelativeDimension D q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D).of_isPullback H ‹_›
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hI : IsIntegral X := GlobalTheory.isIntegral_of_isPullback_of_smooth H
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  exact ⟨hI, hN, hs, GlobalTheory.PosBaseChange.isProjOver_of_isPullback H hP, GlobalTheory.PosBaseChange.surjective_proj H⟩

end GlobalTheory.BaseChangeVariety
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransportStatement
section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  first | exact @GlobalTheory.SqTop.betaArch_of_transport | exact GlobalTheory.SqTop.betaArch_of_transport | (intros; apply GlobalTheory.SqTop.betaArch_of_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigZetaIntegralEqSmulSmallZetaIntegralOfIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigZetaIntegral_eq_smul_smallZetaIntegral_of_integralChange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C]
      (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A' ≃ C₁)
      (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) → gB ∈ KO k A' → c ∈ KO k C →
      ∃ x : kˣ, ValuativeRel.valuation k (x : k) = 1 ∧ ∀ (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Ξ : Matrix (Fin a) C₁ k → ℂ) (Ψ : Matrix A' C₁ k → ℂ),
        bigP (haarVol (KO k (Fin a))) ϖ σ₁ ν β Ξ = smallP (haarVol (KO k A')) σ₁ ν (ν * β) Ψ →
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) =
          (ν x : ℂ) • smallP (haarVol (KO k A')) σ ν (ν * β) fun Y => Ψ (reindex (Equiv.refl _) eC (gB.val * Y * c.val)) := by
  first | exact @GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change | exact GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change | (intros; apply GlobalTheory.TopFlip.ZMatQ.bigZeta_eq_smul_smallZeta_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianFieldDataOfToricRatio
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmAUpper

theorem val_bound_twisted : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF hT w hw i j s Λ Λd z hs1 hs2 hΛ hΛd hz
  obtain ⟨T₀, ψc, T, hv, h0, h0ne, hd, hψ, hT', hΛs⟩ := GlobalTheory.T.toric_ratio_field_data_conjugate p CF d hp hfit hG hF hT w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨lam, a, u, ha, he⟩ := GlobalTheory.T.toric_ratio_field_data_cm p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z
    (by rw [← hd, hz, hΛs]) (GlobalTheory.T.toric_ratio_field_data_abelian p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT')
  obtain ⟨N0, hN⟩ := hfit.1.powers
  exact GlobalTheory.T.twistedThetaValue_valuation_le_div_sq ex.nch w N0 lam a u z (hN w hw a ha) he

end GlobalTheory.ThmAUpper
end
end

