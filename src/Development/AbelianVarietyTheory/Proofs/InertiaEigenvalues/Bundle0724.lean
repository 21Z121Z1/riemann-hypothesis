import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.NgalFil.ENStable_and_jumps | exact GlobalTheory.NgalFil.ENStable_and_jumps | (intros; apply GlobalTheory.NgalFil.ENStable_and_jumps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_rec_compatible : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (w.adicCompletion E)) s, HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  first | exact @GlobalTheory.LocLanglands.charPol_eq_prod_support | exact GlobalTheory.LocLanglands.charPol_eq_prod_support | (intros; apply GlobalTheory.LocLanglands.charPol_eq_prod_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInOfIsCharLab
section
noncomputable section

namespace GlobalTheory.SerSys.OfLabel

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blk_eq_par {a b : ℕ} (x : Gn g a) (y : Gn g b) : blk a b (a + b) x y = par finSumFinEquiv x 0 y := by
  refine Supp.ext_entN fun i j hi hj => ?_
  rw [ParInd.blk_val, entN, dif_pos ⟨hi, hj⟩, ParInd.dg]
  dsimp only
  by_cases h1 : i < a <;> by_cases h2 : j < a
  · rw [(Supp.entN_par _ _ _ i j).1 h1 h2, if_pos ⟨h1, h2⟩]
  · rw [(Supp.entN_par _ _ _ i j).2.2.2 rfl h1 (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [(Supp.entN_par _ _ _ i j).2.1 (by omega) h2, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h2)
    rw [(Supp.entN_par _ _ _ i j).2.2.1, if_neg (by omega), if_pos (by omega)]
    simp

def ofLabel (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) : Sys g where
  e := eSerC L
  idem n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).1
  central n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.1
  orth n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.1
  label n f h := by by_contra h'; exact h ((GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.1 f h')
  sum n := by obtain ⟨S, -, h⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.2; exact ⟨S, h⟩
  mul a b n hn f f' V _ _ ρ v h0 h1 h2 := by
    subst hn
    have hN : ρ.asAlgebraHom (eN g (finSumFinEquiv (m := a) (n := b))) v = v := eN_right _ ρ v fun B => by
      refine h0 _ (fun i j hj hi => ?_) ?_ ?_
      · rw [← ParInd.entN_self (par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b)).val]
        exact (Supp.entN_par _ _ _ i j).2.1 hi hj
      · ext i j
        rw [tl, (Supp.entN_par _ _ _ i j).1 i.2 j.2, ParInd.entN_self]; rfl
      · ext i j
        rw [br, (Supp.entN_par _ _ _ i j).2.2.1, ParInd.entN_self]; rfl
    have hA : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (eSerC L a f)) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h1; exact h1
    have hB : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (eSerC L b f')) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h2; exact h2
    obtain ⟨S, -, hS⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG (a + b)).2.2.2.2
    have hz : ∀ F, F ≠ f * f' → ρ.asAlgebraHom (eSerC L (a + b) F) v = 0 := fun F hF => by
      have hv := ser_vanish' L h5 hG (finSumFinEquiv (m := a) (n := b)) F f f' hF
      have := congrArg (fun z => ρ.asAlgebraHom z v) hv
      simpa only [map_mul, Module.End.mul_apply, hN, hA, hB, map_zero, LinearMap.zero_apply] using this
    have e : v = ∑ F ∈ S, ρ.asAlgebraHom (eSerC L (a + b) F) v := by
      rw [← LinearMap.sum_apply, ← map_sum, hS, map_one, Module.End.one_apply]
    by_cases hm : f * f' ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hm fun F _ hF => hz F hF] at e; exact e.symm
    · rw [Finset.sum_eq_zero fun F hF => hz F (by rintro rfl; exact hm hF)] at e; rw [e]; simp

end GlobalTheory.SerSys.OfLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty.MemberO

variable {D : D7}

set_option maxHeartbeats 1000000 in
theorem live_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem zdecomp_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem chosen_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (S : Set ℂ) :
    Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem goodR_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem taken_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔
      ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ := Iff.rfl

end GlobalTheory.CoefDuty.MemberO

namespace GlobalTheory.CoefDuty.MemberO

set_option maxHeartbeats 1000000 in

theorem contains_fixZ {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hL : Built A M C tup big L) (i : L.X.nd.Loc) :
    Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) := by
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hL
  intro z hz
  obtain ⟨x, hx⟩ := Sp.iq_big i z hz
  refine ⟨x, ?_⟩
  change L.Y.naut.iotaQC i (L.Y.naut.iotaQ i x) = z
  rw [Au.iotaQ, Au.iotaQC]
  exact hx

set_option maxHeartbeats 1000000 in

theorem contains_withLoc {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
    {C : NChoice D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ}
    {L : LocAll (lay0 D)} (hL : Built A M C tup big L) (i : L.X.nd.Loc) :
    Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) :=
  contains_fixZ hL i

theorem member_duties : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := fun _ _ _ _ _ _ _ _ L hL i =>
  ⟨contains_withLoc hL i, contains_fixZ hL i, live_iff L i, zdecomp_iff L i, chosen_iff L i, goodR_iff L i, taken_iff L i⟩

end GlobalTheory.CoefDuty.MemberO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglandsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_local_langlands : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → CuspRead (recT T hL) := by
  first | exact @GlobalTheory.CuspReadTrue.cuspRead_recT | exact GlobalTheory.CuspReadTrue.cuspRead_recT | (intros; apply GlobalTheory.CuspReadTrue.cuspRead_recT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defect_torsion_second_cohomology_kernel : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Pr2d D HW F := by
  first | exact @GlobalTheory.NL.DefectTorsion.defect_torsion | exact GlobalTheory.NL.DefectTorsion.defect_torsion | (intros; apply GlobalTheory.NL.DefectTorsion.defect_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_rec_compatible : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  first | exact @GlobalTheory.lawsLit_det | exact GlobalTheory.lawsLit_det | (intros; apply GlobalTheory.lawsLit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty.LargeRing

theorem evO_laws : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (EvO A M C tup P₁ → EvO A M C tup P₂ → EvO A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → EvO A M C tup P₁ → EvO A M C tup P₂) ∧ (BuiltEx A M C tup → EvO A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → Built A M C tup big' L → Built A M C tup big L := by
  classical
  intro D cf jE A M C tup P₁ P₂
  have anti : ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) →
      Built A M C tup big' L → Built A M C tup big L := by
    intro big big' L h hL
    obtain ⟨Sp, hA, hs⟩ := hL
    exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
  refine ⟨?_, ?_, ?_, anti⟩
  · rintro ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨fun w => b w ∪ c w, fun L hL => ⟨hb L (anti _ _ L (fun _ => Finset.subset_union_left) hL),
      hc L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩⟩
  · rintro h ⟨b, hb⟩
    exact ⟨b, fun L hL => h _ (hb L hL)⟩
  · rintro hE ⟨b, hb⟩ big₀
    obtain ⟨L, hL⟩ := hE fun w => big₀ w ∪ b w
    exact ⟨fun w => big₀ w ∪ b w, L, fun _ => Finset.subset_union_left, hL,
      hb L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩

end GlobalTheory.CoefDuty.LargeRing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam := by
  first | exact @GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | exact GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | (intros; apply GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem semistablePeriodFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨N, F, Y, Z, hY, hZ, hW⟩ := GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods l K bk τ hτ d ρ hρ s
  obtain ⟨F₀, rfl, hε⟩ := GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable l K bk τ hτ d ρ hρ s N F Y Z hY hZ hW
  refine ⟨N, F₀, ?_, ?_⟩
  · exact GlobalTheory.T.semistablePeriodFrame_isDeRham l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε
  · intro hκ
    exact GlobalTheory.T.isCr_of_wSeed_alt l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε hκ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdelesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_levChart | exact GlobalTheory.DownLift.SplitCoef.exists_levChart | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_levChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHom
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvLocalArtin

theorem exists_invLocalArtin : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h art ha
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w
  set f : (w.adicCompletion E)ˣ →* GlobalTheory.HeckeGal.Gab E Ω := art.comp (Neutral.B1.localIdele E w) with hf
  have hfi : Function.Injective f := hinj
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  have ho : ∀ x, ord (w.adicCompletion E) x = Multiplicative.toAdd (o x) := fun _ => rfl
  have unit_iff : ∀ x, Formalism.L2.Host.IsUnitAt w x ↔ ord (w.adicCompletion E) x = 0 := by
    intro x
    unfold Formalism.L2.Host.IsUnitAt
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj]
    omega
  have unif_ord : ∀ x, Formalism.L2.Host.IsUnifAt w x → ord (w.adicCompletion E) x = 1 := by
    intro x hx
    unfold Formalism.L2.Host.IsUnifAt at hx
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, WithZero.exp_inj] at hx
    omega

  obtain ⟨π, hπ, hπf⟩ := (ha.frob w A h (GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)⁻¹)).2 ⟨_, isFrob_frob, rfl⟩
  have hπo : ord (w.adicCompletion E) π = 1 := unif_ord π hπ
  have hπf' : f π⁻¹ = GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω) := by
    rw [map_inv]; show (art (Neutral.B1.localIdele E w π))⁻¹ = _; rw [hπf, map_inv, inv_inv]
  have ordpow : ∀ n : ℤ, ord (w.adicCompletion E) (π⁻¹ ^ n) = -n := by
    intro n
    rw [ho, map_zpow, map_inv, toAdd_zpow, toAdd_inv, ← ho, hπo]; simp
  have hex : ∀ σ : Weil h, ∃ x, ord (w.adicCompletion E) x = -deg σ ∧ f x = GlobalTheory.HeckeGal.toAb E Ω σ := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    obtain ⟨u, hu, huf⟩ := (ha.ine w A h (GlobalTheory.HeckeGal.toAb E Ω τ)).2 ⟨τ, τ.2, rfl⟩
    refine ⟨π⁻¹ ^ deg σ * u, ?_, ?_⟩
    · rw [SmGL.ord_mul, ordpow, (unit_iff u).1 hu, add_zero]
    · rw [map_mul, map_zpow, hπf']
      show _ * art (Neutral.B1.localIdele E w u) = _
      rw [huf, ← map_zpow, ← map_mul]
      congr 1
      conv_rhs => rw [hτ]
      simp [Subgroup.coe_mul, Subgroup.coe_zpow]
  choose g hgo hgf using hex
  let a : Weil h →* (w.adicCompletion E)ˣ :=
    { toFun := g
      map_one' := hfi (by rw [hgf, map_one, Subgroup.coe_one, map_one])
      map_mul' := fun σ τ => hfi (by rw [hgf, map_mul, hgf, hgf, Subgroup.coe_mul, map_mul]) }
  refine ⟨a, ?_, hgo, fun σ => hgf σ⟩
  intro x
  set n := ord (w.adicCompletion E) x
  have hu : Formalism.L2.Host.IsUnitAt w (x * π⁻¹ ^ n) := by
    rw [unit_iff, SmGL.ord_mul, ordpow]; simp [n]
  obtain ⟨τ, hτ, hτf⟩ := (ha.ine w A h (f (x * π⁻¹ ^ n))).1 ⟨_, hu, rfl⟩
  refine ⟨ineIncl h ⟨τ, hτ⟩ * frob h ^ (-n), hfi ?_⟩
  show f (g _) = f x
  rw [hgf, Subgroup.coe_mul, Subgroup.coe_zpow, coe_ineIncl, map_mul, map_zpow, hτf, ← hπf', ← map_zpow, ← map_mul]
  congr 1
  rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]

end GlobalTheory.InvLocalArtin
end
end

