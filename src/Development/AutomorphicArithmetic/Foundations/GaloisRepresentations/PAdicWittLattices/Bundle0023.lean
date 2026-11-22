import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0011
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0012
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0013
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowPiece
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.CechHEquivCohOnCechCubeMapOver
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOfPf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.Bundle0001

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateDiff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateDiff :
    TateDiff := by
  intro p _ D G L R _ _ gb S s N o k _ _ t I J hI hJ
  have hN : 0 < N.1 := by have := N.2.1; omega
  have hNp : N.1.Coprime p := N.2.2
  obtain ⟨g, hg⟩ := GlobalTheory.LKGeo.GammaUniq.exists_simSys_all hN hNp
    (fun n q q' z z' h h' => GlobalTheory.weilIs_unique_fieldPoint S o.A _ (LB.isLB_pull o.isLB _) k t n q q' z z' h h')
    (GenCmp.tateRestrict J) (GenCmp.tateRestrict I)
    (fun y => (hJ y).symm.trans (hI y))
  obtain ⟨u, hu, hh⟩ := GlobalTheory.T.similitude_action_adelic_lattice p D G L N.1 hN hNp g
  refine ⟨u, hu, fun n hn hc x y => ?_⟩
  have e₁ : I.ev n x = J.ev n (g.g n x) := hg n hn hc x
  have e₂ : ∀ a b : D.La, J.ev n a = J.ev n b ↔ ∃ z, a = b + n • z := fun a b =>
    GlobalTheory.UPel.HT.TateCompare.ev_eq_iff (GenCmp.tateRestrict J) hn hc
  obtain ⟨w, hw, e₃⟩ := hh n hn hc x
  let f : D.La →+ (AfP p ⊗[ℚ] VQ D) := AddMonoidHom.mk' (inAf D) (GlobalTheory.LKGeo.GammaUniq.inAf_add (p := p) (D := D))
  have hf : ∀ a, f a = inAf D a := fun _ => rfl
  rw [Category.comp_id, e₁, e₂]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inAf D z + w, add_mem (GlobalTheory.LKGeo.GammaUniq.inAf_mem z) hw, ?_⟩
    rw [e₃, hz, ← hf, ← hf, ← hf, map_add, map_nsmul, smul_add, add_assoc]
  · rintro ⟨v, hv, e₄⟩
    have e₅ : inAf D (g.g n x - y) = n • (v - w) := by
      rw [← hf, map_sub, hf, hf, smul_sub]
      rw [e₃] at e₄
      rw [sub_eq_sub_iff_add_eq_add, e₄, add_comm]
    obtain ⟨z, hz⟩ := GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hc _ (sub_mem hv hw) e₅
    exact ⟨z, by rw [← hz]; abel⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem oActN_act_natCast_eq_one_pow {S : Scheme} {O : Type} [Ring O] {G : Over S} [GrpObj G]
    (a : GlobalTheory.UPel.HT.OActN O G) (n : ℕ) : a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (· * (a.act 0)⁻¹) h
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    rw [Nat.cast_zero, pow_zero]
    exact h2.symm
  | succ n ih =>
    rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem UpperTheory.Gal.G3.pTransDeep :
    SysOf → AdmOf → FullOf → RelArith → TransDeep := by
  intro hSys hAdm hFull hRel p _ D G L R _ _ gb h hI
  obtain ⟨f, u, c, k, hsys, hm, hk, hf⟩ := hSys p D G L h hI
  obtain ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ := hsys
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left p |>.mp hkp) (Fact.out : Nat.Prime p).one_lt.ne'
    · exact hpos
  refine ⟨k, hkp, fun N => hAdm p D G L h k N hI hk0 hk, ?_⟩
  intro N S _ s o'
  have hρ : gb.ρ = (RingHom.id R) (GenCmp.baseOf gb).ρ := rfl
  have ht : ∀ i, gb.t i = (RingHom.id R).comp ((GenCmp.baseOf gb).t i) := fun i => rfl
  let o1 := GenCmp.toObj hρ ht o' (GenCmp.genericObject_kernelCondition o')
  obtain ⟨o2, ψ, hψm, hψa, hψe, hgal, ⟨hlb⟩, -⟩ :=
    GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base p D R (GenCmp.baseOf gb) f u c k N N.2.1 N.2.2 hc hkp hck hlin hcomp hEF hsurj S _ o1
  let o3 := GenCmp.rebase (t := s) hρ ht rfl o2
  let o : GObj gb N s := GenCmp.toGObj o3 (GenCmp.geomFull N.2.2 o3)
  refine ⟨o, ψ, ?_⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  haveI := hψm
  haveI : Epi (Over.Hom.left ψ) := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
  haveI : Epi ψ := Over.epi_of_epi_left ψ
  obtain ⟨ψ', hψ'm, hψψ'⟩ := GlobalTheory.HomDescent.exists_desc S o1.A o2.A o1.A
    (HeckeAd.heckeSubA o1 (f (↑N * k)) ↑N) ψ hψm hgal (o1.act.act (k : D.O)) (o1.act.hom _)
    (fun g hg => by
      rw [oActN_act_natCast_eq_one_pow, comp_pow, Category.comp_id, HeckeAd.pow_eq_one_of_mem o1 _ g hg])
  refine ⟨hψm, hψa, ⟨ψ', k, hψ'm, ?_, ?_, ?_, hkp⟩, ?_, ?_⟩
  · intro a
    change o2.act.act a ≫ ψ' = ψ' ≫ o1.act.act a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, ← hψa a, Category.assoc, hψψ', ← Category.assoc, hψψ',
      ← o1.act.mul, ← o1.act.mul, Nat.cast_comm]
  · change ψ ≫ ψ' = 𝟙 o1.A ^ k
    rw [hψψ', oActN_act_natCast_eq_one_pow]
  · change ψ' ≫ ψ = 𝟙 o2.A ^ k
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψψ', oActN_act_natCast_eq_one_pow, pow_comp, comp_pow, Category.id_comp,
      Category.comp_id]
  · obtain ⟨t, t', ht1, ht2, ht3, ht4⟩ := hm
    exact ⟨k ^ 2 / c, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (Nat.Coprime.pow_left 2 hkp),
      ⟨hlb⟩, t, t', ht1, ht2, ht3, ht4⟩
  · intro kk _ _ t β htβ
    obtain ⟨I', hI'⟩ := o'.geom kk t β htβ
    obtain ⟨J0, hJ0e, hJ0r⟩ := HeckeAd.TateTranslAt.exists_tateIsoO_of_given D (GenCmp.baseOf gb) f u c k
      N hc hkp N.2.1 N.2.2 hck hlin hcomp hEF hsurj o1 o2.A o2.act ψ o2.ab hψm hgal hψa o2.P o2.isLB hlb
      kk t β (GenCmp.tateRestrict I') (fun y => hI' y)
    obtain ⟨I'', hI''⟩ := hFull p D R gb S s N o kk t J0
    have hNpos : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    refine ⟨I', I'', hI', fun y => ?_, ?_⟩
    · rw [hI'' _ hNpos N.2.2, ← hJ0e y]
      change toUnit (Over.mk t) ≫ o2.eta y = _
      rw [hψe y]
    · exact hRel p D G L R gb S s N (↑N * k) o' o kk t I' I'' ψ h f u c k hψm hI
        ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ hf
        (fun n hn hnp x => by rw [hI'' n hn hnp]; exact hJ0r n hn hnp x)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TraceSplitHolds
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem seamHopEx_holds : UpperTheory.Gal.Seam.HopEx := by
  intro l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap k Ω) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  exact (hopSpec_holds l hl H Ω g d hd).1

theorem locTower_holds : UpperTheory.Gal.Seam.LocTower := locTower_of vBcS_holds seamHopEx_holds UpperTheory.Gal.Seam.niceBc

theorem traceSplit_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.TraceSplit := by
  intro k _ Z Y W q s _ _ c _ _ I _ σ hσ hS a b y
  exact hodgeTr_holds k a b q (s ≫ q) s rfl W (c ≫ q) c rfl I σ hσ hS y

theorem hodgeBC_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC :=
  jHBC jHBasis jHEquiv jHCube jHAffine jHCover (jHOmega jHEquiv jHForms jHSections jHAffine) PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.cech_holds
    (jHTrace jHFun jHAffine)

theorem coverOp_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := jCoverOp etnGood_holds @bcSplits_holds @bcGal_holds corrUniq_holds

theorem lowHodge_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge :=
  jLowHodge hodgeGood_holds @bcGood_holds.{0} fEtBasic_holds
    (jHodgeOpBc @bcSplits_holds hodgeTr_holds (jTrBc.{0} @bcSplits_holds)) @coverInv_holds.{0} @liesOp_holds.{0}

theorem hopLies_holds : HopLies := jHopLies etGood_holds @bcGood_holds.{1} fEtBasic_holds hopSpec_holds @liesOp_holds.{1}

theorem lowPiece_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := jLowPiece hopLies_holds pieceLe_holds

theorem lowCov_holds : LowCov :=
  jLowCov @galClosD_holds @bcSplits_holds @bcGal_holds @jGenIso (jModBc UpperTheory.Gal.Seam.goodOf)

theorem jumpStep_of (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (hC : CrysStep) (hR : RepEx) : JumpStep :=
  PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpStep_of
    (PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpCore_of hS (jLowNice fEtBasic_holds) lowHodge_holds lowPiece_holds (matEx_of hR)
      (jLocalMat UpperTheory.Gal.Seam.niceBc seamHopEx_holds locTower_holds) (coverLow_of_cov PositivityTheory.AutomorphicGaloisHodgeTate.G8.coverOf lowCov_holds)
      (jBridgeInt UpperTheory.Gal.Seam.intMap) (jBCTower UpperTheory.Gal.Seam.niceBc)
      (PositivityTheory.AutomorphicGaloisHodgeTate.G8.locE_of hodgeBC_holds traceSplit_holds coverOp_holds) PositivityTheory.AutomorphicGaloisHodgeTate.G8.OccMove_holds
      PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpsEx_holds jConjBridge jJumpOfHT2) hC

end UpperTheory.Gal.G3
end

