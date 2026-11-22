import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0010
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesExplicit
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  have hi0 : i ≤ D.R.m := Nat.le_of_succ_le hi
  have hlt : i < D.R.m := hi
  have h1 : (1 : GL (Fin (D.R.N i)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi0) := one_mem _
  have h1' : (1 : GL (Fin (D.R.N (i + 1))) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) := one_mem _
  have hx : ((St i hi0).y c).1 = ratA D.host.F (1 : GL (Fin (D.R.N i)) D.host.E) * ((St i hi0).y c).1 * (1 : ((St i hi0).K ((St i hi0).chOf c)).lev.U).1 := by
    simp
  have hx' : ((St (i + 1) hi).y c').1 = ratA D.host.F (1 : GL (Fin (D.R.N (i + 1))) D.host.E) * ((St (i + 1) hi).y c').1 * (1 : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U).1 := by
    simp
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie (i + 1) hi 1 h1'
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie i hi0 1 h1
  have hl := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie i hi0 c ((St i hi0).y c) 1 h1 1 hx
  have hl' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie (i + 1) hi c' ((St (i + 1) hi).y c') 1 h1' 1 hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hTie Xi muT hL i hi c c' ((St i hi0).y c) ((St (i + 1) hi).y c') 1 h1 1 h1' 1 1 hx hx' hu'
  have hloc := hL.loc i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c')
  rw [hl, hl'] at hloc
  refine GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes D t.cc (ssRec t u μ) (t.rd u μ).lev _ _ (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x)) _ _ hu hu' ?_
  have hE : Xi i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c') = _ := funext fun z => by
    have := hd z
    simpa [(hL.mu_mul i hlt).1, -Matrix.toLin'_toMatrix'] using this
  rw [hE] at hloc
  exact hloc

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.HeckeClose

theorem heckeClose : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).PartsW false → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hH hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hJ hSer hPass hU hGU hGE hLW hA hB hPos hParts
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCD D
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨tr, htr⟩ := GlobalTheory.T.exists_separating_inert_eigenvalue_passage hH R F hLI hC hEx hS hJ hX hB hPos
  have hTS : A3.fam3.TypesSep3 :=
    GlobalTheory.T.finite_types_separated_by_inert_places hCD hH R F hLI hOk hC hEx ⟨fun t k => hJ.R t k.1 k.2, fun j t k => hJ.L j t k.1 k.2⟩ hPass hPos hB
  have hG : GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes R F hC s hOk hSer).2
  have hR := GlobalTheory.T.exists_hecke_operators_rows_intertwine_theta_lifts hH hHC hCD R F hLI hC hEx hJ hB hPos
  have hL := GlobalTheory.T.heckeTheta_level3_exists hH hHC hCD R F hLI hC hEx hJ s hOk hG hU hGU hGE hLW hA hPos hB hParts hTS hPass
  exact ⟨GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk R F hC hJ, ⟨hR, hL⟩, hTS, tr, htr⟩

end GlobalTheory.Hk3.HeckeClose

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.L2.DIV

namespace GlobalTheory.KerJ.ColSideHyp

theorem plc_dvd_iff' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem g_not_mem_Qp (t : KerEntTied ex) (hC : GlobalTheory.KerJ.ColSide t) (μ : D.what₂.Tup) (k : Fin 2) : D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hC.sel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff' v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff' v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hC.bad.1 k
  · simp at hPQ

end GlobalTheory.KerJ.ColSideHyp

namespace GlobalTheory

theorem colSide_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t hC hTop
  obtain ⟨eta, hTied⟩ := hC.chars
  rw [t.glob_σ] at hTied
  refine GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions D L hT Gi Gl K Y cX ex t (fun j => ⟨_, hTied.mu0 j⟩) (fun j v hv => hTied.muVal j v hv) ?_ hTop
  intro μ k
  exact GlobalTheory.KerJ.ColSideHyp.g_not_mem_Qp t hC μ k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TieBase

theorem base_data : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  intro D L hT Gi Gl Kc Dx cX ex t
  have h0 : t.δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D t.cc t.δ t.B
  refine ⟨h0, t.B.latAll t.cc_ok t.δ_ok h0, ?_, GlobalTheory.Mem.NatEqui.eqP D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok⟩
  exact GlobalTheory.ColNorms.familyVectors D t.cc t.δ t.B t.χ (Formalism.MainNotions.GL3Theta.cm_field_facts_hold D) (Formalism.MainNotions.GL3Theta.induced_cm_type D) t.cc_ok t.δ_ok t.χ_ok
    (GlobalTheory.ExponentsFinite.yFinite D _ t.B.kc)

end GlobalTheory.TieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeEqAwayFromPrimeOfAgreeOffPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_eq_away_from_prime_of_agree_off_place : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  first | exact @GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | exact GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatKRatMulLev
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

set_option maxHeartbeats 1000000 in

theorem cmpLite_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  intro D N h c Tw u μ w hg Fl Lv Ch H
  exact H

end GlobalTheory.Svd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompatStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_comp_norm_compat : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  first | (exact @GlobalTheory.ArtinNormU.localArtin_normU) | (exact GlobalTheory.ArtinNormU.localArtin_normU) | (intros; apply GlobalTheory.ArtinNormU.localArtin_normU  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalarStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
theorem _root_.GlobalTheory.T.localOperator_acts_by_localComponentScalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  first | exact @GlobalTheory.Cong.opOf_locU_eq_smul | exact GlobalTheory.Cong.opOf_locU_eq_smul | (intros; apply GlobalTheory.Cong.opOf_locU_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlace
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct Matrix

namespace GlobalTheory.LatAway

theorem mapRingHom_comp_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) :
    (RingOfIntegers.mapRingHom (σ : E →+* E)).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := by
  refine RingHom.ext fun r => RingOfIntegers.ext ?_
  have h : ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (r : F) := rfl
  simp only [RingHom.comp_apply]
  rw [show ((RingOfIntegers.mapRingHom (σ : E →+* E) (algebraMap (𝓞 F) (𝓞 E) r) : 𝓞 E) : E) =
    σ ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) from rfl, h]
  exact σ.commutes _

theorem seam_locP_inj {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (N N' : Submodule (𝓞 X.E) (Sp X.E n))
    (h : Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N')) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  let ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let f : Sp X.E n →ₛₗ[(ψ : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) :=
    { toFun := fun x l => s.iE (x l)
      map_add' := fun x y => by funext l; simp
      map_smul' := fun r x => by
        funext l
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl }
  have hlat : ∀ M : Submodule (𝓞 X.E) (Sp X.E n), s.lat M = M.map f := by
    intro M
    unfold Seam.lat
    rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = f '' M from rfl, ← Submodule.map_coe]
    exact Submodule.span_eq _
  have hinj : Function.Injective f := by
    intro x y hxy
    funext l
    exact s.iE.injective (congrFun hxy l)
  have hloc : ∀ M : Submodule (𝓞 X.E) (Sp X.E n),
      Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map f) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map f := by
    intro M
    ext x
    constructor
    · rintro ⟨r, hr, z, hz, hzx⟩
      have hfy : f (fun l => s.iE.symm (x l)) = x := by
        funext l
        show s.iE (s.iE.symm (x l)) = x l
        simp
      refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
      · intro hm
        apply hr
        have := (mem_seamP s P (ψ.symm r)).2 hm
        simpa [ψ] using this
      · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
          apply hinj
          rw [f.map_smulₛₗ, hfy, hzx]
          show ψ (ψ.symm r) • x = r • x
          rw [RingEquiv.apply_symm_apply]
        rw [this]
        exact hz
    · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
      refine ⟨ψ r, ?_, r • y, hy, ?_⟩
      · intro hm
        exact hr ((mem_seamP s P r).1 hm)
      · rw [f.map_smulₛₗ]
        rfl
  rw [hlat, hlat, hloc, hloc] at h
  exact Submodule.map_injective_of_injective hinj h

theorem locP_map_equiv {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem locP_mvL {E : Type} [Field E] {N : ℕ} (g : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (h : Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ') :
    Formalism.HermitianLatticesTheory.localization₂ q (mvL g Λ) = Formalism.HermitianLatticesTheory.localization₂ q (mvL g Λ') := by
  show Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (((toLE g).restrictScalars (𝓞 E) : (Fin N → E) ≃ₗ[𝓞 E] (Fin N → E)) : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))) =
    Formalism.HermitianLatticesTheory.localization₂ q (Λ'.map (((toLE g).restrictScalars (𝓞 E) : (Fin N → E) ≃ₗ[𝓞 E] (Fin N → E)) : (Fin N → E) →ₗ[𝓞 E] (Fin N → E)))
  rw [locP_map_equiv, locP_map_equiv, h]

theorem latAd_fg_of_latCo {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E))
    (h : (latCo sp J co a y Lb).FG) : (latAd y Lb).FG := by
  have h1 : (mvL co⁻¹ (latCo sp J co a y Lb)).FG := h.map _
  haveI := isNoetherian_of_fg_of_noetherian _ h1
  refine Submodule.FG.of_le_of_isNoetherian (T := mvL co⁻¹ (latCo sp J co a y Lb)) ?_
  unfold latCo
  rw [← mvL_mul, inv_mul_cancel]
  have h2 : mvL (1 : GL (Fin N) E) (compan (sp := sp) J a (latAd y Lb)) = compan (sp := sp) J a (latAd y Lb) := by
    unfold mvL
    convert Submodule.map_id _
    refine LinearMap.ext fun z => ?_
    show toLE 1 z = z
    rw [toLE_apply, Units.val_one, Matrix.one_mulVec]
  rw [h2]
  exact le_sup_left

theorem seam_lat_fg {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (h : N.FG) :
    (s.lat N).FG := by
  let f : Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) :=
    { toFun := fun x l => s.iE (x l)
      map_add' := fun x y => by funext l; simp
      map_smul' := fun r x => by
        funext l
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl }
  have e : s.lat N = N.map f := by
    unfold Seam.lat
    rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (N : Set (Sp X.E n))) = f '' N from rfl, ← Submodule.map_coe]
    exact Submodule.span_eq _
  rw [e]
  exact h.map f

theorem locP_companion {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ : Λ.FG) (hΛ' : Λ'.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ')
    (h' : Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ') :
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') :=
  GlobalTheory.T.primeLocalization_companionLattice_eq_of_localizations sp J a q Λ Λ' hΛ hΛ' h h'

theorem mem_latAd_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (w : Fin N → E) :
    w ∈ latAd y Lb ↔ ((y⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun a => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (w a)) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  unfold latAd
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      rw [show (fun a : Fin N => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((0 : Fin N → E) a)) = 0 from
        funext fun a => map_zero _, Matrix.mulVec_zero]
      exact zero_mem _
    | add z z' _ _ hz hz' =>
      rw [show (fun a : Fin N => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((z + z') a)) =
        (fun a => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) + (fun a => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z' a)) from
        funext fun a => map_add _ _ _, Matrix.mulVec_add]
      exact add_mem hz hz'
    | smul c z _ hz =>
      have hc : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((c : 𝓞 E) : E) ∈ Formalism.L2.Herm.intAf F E :=
        Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
      rw [show (fun a : Fin N => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((c • z) a)) =
        Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((c : 𝓞 E) : E) • (fun a => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) from
        funext fun a => by simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul], Matrix.mulVec_smul]
      exact (Formalism.L2.Herm.hatL (F := F) Lb).smul_mem (⟨_, hc⟩ : Formalism.L2.Herm.intAf F E) hz
  · intro hw
    exact Submodule.subset_span hw

theorem exists_awayScale {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hk : bc (prV (E := E) v) k = 1) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb :=
  GlobalTheory.T.adelicMatrix_one_at_place_scaled_preserves_completedLattice Lb hfg hsp v k hk

theorem locP_latAd_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) (q : Ideal (𝓞 E)) [q.IsPrime]
    (hq : q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) :
    Formalism.HermitianLatticesTheory.localization₂ q (latAd x Lb) ≤ Formalism.HermitianLatticesTheory.localization₂ q (latAd x₁ Lb) := by
  obtain ⟨t, ht, hk⟩ := exists_awayScale Lb hfg hsp v (x₁⁻¹ * x) (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rintro w ⟨s, hs, hw⟩
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t * s, ?_, ?_⟩
  · intro hm
    rcases (inferInstance : q.IsPrime).mem_or_mem hm with h1 | h1
    · exact ht (by rw [← hq]; exact h1)
    · exact hs h1
  · rw [mem_latAd_iff] at hw ⊢
    have e1 := hk _ hw
    convert e1 using 1
    have hxx : ∀ z : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
        (x : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
          ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hxx, ← Matrix.mulVec_smul]
    congr 1
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]

end GlobalTheory.LatAway

namespace GlobalTheory.LatAway
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Forms

def placeUnder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

theorem decoAt_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ p p₁ hp hp₁ P hx
  set Q := seamP t.seam P.1 with hQ
  have hxv := hx (placeUnder Q) rfl
  set Lb := ((St i hi).K β).lev.Lb with hLb
  have hfin : Lb.FG := (Module.Finite.iff_fg).1 ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have hfg : (latAd x.1 Lb).FG :=
    latAd_fg_of_latCo _ _ _ _ _ _ (hp.lat ▸ seam_lat_fg t.seam _ p.deco.2.lat.fg)
  have hfg₁ : (latAd x₁.1 Lb).FG :=
    latAd_fg_of_latCo _ _ _ _ _ _ (hp₁.lat ▸ seam_lat_fg t.seam _ p₁.deco.2.lat.fg)
  have key : ∀ (q : Ideal (𝓞 D.host.E)) [q.IsPrime], q.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = (placeUnder Q).asIdeal →
      Formalism.HermitianLatticesTheory.localization₂ q (latAd x₁.1 Lb) = Formalism.HermitianLatticesTheory.localization₂ q (latAd x.1 Lb) := by
    intro q _ hq
    exact le_antisymm (locP_latAd_le Lb hfin hsp x₁.1 x.1 _ q hq hxv.symm) (locP_latAd_le Lb hfin hsp x.1 x₁.1 _ q hq hxv)
  have hσ : (Q.asIdeal.comap (RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E))).comap
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = (placeUnder Q).asIdeal := by
    rw [Ideal.comap_comap, mapRingHom_comp_algebraMap]
    rfl
  have e := locP_mvL (A.crd i hi) Q.asIdeal _ _
    (locP_companion D.sp (gramN D i hi) a Q.asIdeal _ _ hfg₁ hfg (key _ rfl) (key _ hσ))
  apply seam_locP_inj t.seam P.1
  rw [hp.lat, hp₁.lat]
  exact e

end GlobalTheory.LatAway
end
end

