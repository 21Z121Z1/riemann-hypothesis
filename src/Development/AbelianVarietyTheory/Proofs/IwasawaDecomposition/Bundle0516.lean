import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0510
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainsLevelStructureCompatibleAtLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem exists_lvTied_of_std {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type)
    (chOf : (I.stp u a i).Cl → Ch)
    (lat' : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hlat : lat' = I.latAt u a i)
    (res' : ∀ v : (I.atT l u a).vT, 𝓞 B.host.E →+* (I.atT l u a).Fv v) (hres : res' = I.resT l u a)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (lat' c.1)))
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi)
    (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal})
    (hK : ∃ k, I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hY : ∀ y, (eY y).1 = y.1) (hV : ∀ v, (eV v).1 = v.1.under (𝓞 B.host.F))
    (hkill : ∀ β, FunKilled (K β).lev (X.piT u)) :
    ∃ L : LevelCompatibleLattices (D := I.rec7 l Z) (I.fm l u a) (B.T u) res' i hi (fun c => latCrd (I.rec7 l Z) i hi (lat' c)),
      ((∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.N), L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
        ∀ v c z (h : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.dnN v), L.prk v c z = Submodule.Quotient.mk ⟨z.1, h⟩) ∧
      (∃ fMe, FvTieG L eV K fMe) ∧ UpNatTieG L eY eV K ∧ DnNatTieG L eY eV K := by
  subst hlat hres
  obtain ⟨L, hL⟩ := GlobalTheory.Mem.Col2.TC.exists_level_projections I hOk hP l Z u a i hi
  have hK' : I.ReadsK l Z u a i hi chOf K := hK
  obtain ⟨fMe, hf, -⟩ := GlobalTheory.Mem.Col2.LevFun.fvTieG I hOk hP l Z u a i hi bad Ch chOf K eV L hK' hV hL
    (fun β v h t t' e => hkill β v h t t' e)
  exact ⟨L, hL, ⟨fMe, hf⟩, GlobalTheory.Mem.Col2.UpChart.upNatTie I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK' hY hV hL,
    GlobalTheory.DnMove.dnNatTieG_cols I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK' hY hV hL⟩

set_option maxHeartbeats 4000000 in

noncomputable def lvSameMu0 {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l)
    (u : B.Word) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m)
    (a : TwAtT (I.tw l l0 Z) u (I.rec7 l Z).what₂.mu0) (hV : a.eVT = Equiv.refl _)
    (hR : ∀ v r, (a.eFv v).symm (I.resT l u I.mu0 (a.eVT v) r) = I.resT l u I.mu0 v r) :
    LvSame a i (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i) (Formalism.L2.Herm.yCast (I.rec7 l Z) u i) ((I.tw l l0 Z).eMu0 u i hi) := by
  obtain ⟨eVT, eFv, psiT, rhoT, Mu0, duStar, Dstar, GamP, tauOf, seenP⟩ := a
  dsimp only at hV hR
  subst hV
  have hE : ∀ v x, eFv v x = x := by
    intro v x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (congrArg (eFv v) (hR v r)).symm.trans ((eFv v).apply_symm_apply _)
  exact
    { eLv := fun v c => AddEquiv.refl _
      eLv_smul := fun v c r x => by rw [hE]; rfl
      fv := fun v c x => by rw [hE]; rfl
      up := fun v c x _ => rfl
      upT := fun v c x _ h y => rfl
      eLk := fun v c => AddEquiv.refl _
      eLk_smul := fun v c r x => by rw [hE]; rfl
      te := fun v c => rfl
      dn := fun v c g g' hg _ => by
        obtain rfl : g = g' := LinearMap.ext fun x => (hE v (g x)).symm.trans (hg x)
        rfl
      dnT := fun v c g g' hg _ h y => by
        obtain rfl : g = g' := LinearMap.ext fun x => (hE v (g x)).symm.trans (hg x)
        rfl
      dil := fun v r c => by
        have key : ∀ q : (((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v)ˣ, (q : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) = (r : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) →
            ((I.tw l l0 Z).fm u (I.rec7 l Z).what₂.mu0).dil i v r (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i c) =
              Formalism.L2.Herm.clsCast (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dil i v q c) := by
          intro q hq
          obtain rfl : q = r := Units.ext hq
          rfl
        refine key _ ?_
        exact hE v _
      dilT := fun v r c h y => by
        have key : ∀ q : (((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v)ˣ, (q : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) = (r : ((I.tw l l0 Z).A u (I.rec7 l Z).what₂.mu0).Fv v) →
            ((I.tw l l0 Z).fm u (I.rec7 l Z).what₂.mu0).dilT i v r (Formalism.L2.Herm.clsCast (I.rec7 l Z) u i c)
              (fun z => h ((Formalism.L2.Herm.yCast (I.rec7 l Z) u i).symm z)) (Formalism.L2.Herm.yCast (I.rec7 l Z) u i y) =
              ((I.rec7 l Z).fm u).dilT i v q c h y := by
          intro q hq
          obtain rfl : q = r := Units.ext hq
          rfl
        refine key _ ?_
        exact hE v _
      bw := fun w _ _ v x => Iff.rfl }

set_option maxHeartbeats 4000000 in

theorem tw_lv_tied_and_same : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → (∃ Lv : SymmetricTwistedLevelData W, I.StdLv l Z l0 Lv) ∧ Nonempty (TwLvSameS W) := by
  intro B X I hOk hP l Z l0 inQ H F T J W hF hW
  have hY : ∀ u μ i hm y, (twYS T F u μ i hm y).1 = y.1 := by
    intro u μ i hm y
    unfold twYS
    rw [hW.eY u μ i hm]
    simp only [Equiv.trans_apply, Equiv.refl_symm, Equiv.refl_apply]
    unfold eYS
    split_ifs with h
    · exact (hF u).1.eY i hm h y
    · have e : (I.rec7 l Z).R.m = B.R.m := rfl
      exact (hF u).1.eYC i (by omega) (by omega) y
  have hV : ∀ u μ v, ((W.atT u μ).eV (F u).atT v).1 = v.1.under (𝓞 B.host.F) := by
    intro u μ v
    unfold TwAtT.eV
    rw [hW.eVT u μ]
    exact (hF u).1.eV v
  have hres : ∀ u μ, (W.atT u μ).res (F u).atT = I.resT l u μ := fun u μ =>
    funext fun v => RingHom.ext fun r => hW.eFv u μ v r
  have key := fun u μ (hμ : μ ≠ (I.rec7 l Z).what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) =>
    exists_lvTied_of_std I hOk hP l Z u μ i hm _ _ (T.chOf u μ i) (T.lat u μ i) (hW.lat u μ i) ((W.atT u μ).res (F u).atT) (hres u μ)
      (W.ch u μ hμ i h1 hm) (twYS T F u μ i hm) ((W.atT u μ).eV (F u).atT) (hW.reads u μ hμ i h1 hm) (hY u μ i hm) (hV u μ)
      (hW.killed u μ hμ i h1 hm)
  choose L hL using key
  refine ⟨⟨⟨L, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.1.choose, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.1.choose_spec,
    fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.2.1, fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).2.2.2, ?_⟩,
    fun u μ hμ i h1 hm => (hL u μ hμ i h1 hm).1⟩, ⟨⟨?_, ?_⟩⟩⟩
  · intro u μ hμ i h1 hm
    rw [hres u μ, hW.lat u μ i]
    exact GlobalTheory.Mem.Col2.TC.bw_tie I hOk hP l Z u μ i hm (twYS T F u μ i hm) (hY u μ i hm)
  · intro u μ
    rw [hW.eCls0 u μ, hW.eY u μ 0 (Nat.zero_le _)]
    refine (GlobalTheory.Mem.Col2.TC.StepZero.lvSame_zero I hOk hP l Z l0 u μ (W.atT u μ) (hW.eVT u μ) fun v r => ?_).some
    have h := hW.eFv u μ v r
    simp only [TwAtT.res, RingHom.comp_apply, (hF u).1.res] at h
    exact h
  · intro u i hi
    refine lvSameMu0 I l Z l0 u i hi (W.atT u _) (hW.eVT u _) fun v r => ?_
    have h := hW.eFv u (I.rec7 l Z).what₂.mu0 v r
    simp only [TwAtT.res, RingHom.comp_apply, (hF u).1.res] at h
    exact h

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleLayerCompatibilitiesOfXPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  intro B X I hI hP l Z l0 inQ H F T J W Lv hQ hF hW hLv hTop
  have hQ' : ∀ a v, v ∈ T.Q a ↔ I.UnderQ a v := fun a v => (T.Q_iff a v).trans (hQ a v)
  have hC := fun u a => GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison I hI hP l Z u a (T.Q a) (F u).clsP (hQ' a) (J.Q_off u a) (hF u).1.what₂
  choose K hLb hfin hrd hU hchi using hC
  have hV := fun u a => GlobalTheory.T.formsX_tupleChain_of_levelReading I hI hP l Z u a (T.Q a) (K u a) (hQ' a) (J.Q_off u a) (hrd u a)
  choose V hN hE using hV
  choose k hk hkT using hTop
  have hTil := fun u a ha h1 => GlobalTheory.Mem.Col2.TwP.til_tw I hI hP l Z hF hW hLv u a ha h1 (K u a) (hrd u a) (hk u a ha h1) (hkT u a ha h1)
  choose Tl hz hev using hTil
  choose jM hj0 hj1 hj2 hj3 hj4 using fun u a => GlobalTheory.Mem.Col2.PerConj.period_conj I hI hP l Z u a
  let Pt : TwPTiedS Lv :=
    { cls := fun u a _ => K u a
      Lb := fun u a _ => hLb u a
      chi_fin := fun u a _ => hfin u a
      val := fun u a _ => V u a
      norm := fun u a _ => hN u a
      til := fun u a ha h1 => Tl u a ha h1 }
  let E : TwPEvzS Pt :=
    { eWz := fun u a => LinearEquiv.refl ℂ _
      evz := fun u a ha h1 φ c s s' hs => hev u a ha h1 φ c s s' hs
      jM := jM
      per := fun u a _ => ⟨hj1 u a, hj2 u a, hj3 u a⟩ }
  refine ⟨Pt, E, ⟨fun u a _ v hv => hU u a v hv, fun u a _ κ κ' h h' => hchi u a κ κ' h h'⟩, ⟨fun u a _ => hrd u a, fun u a _ z c s s' h => hE u a z c s s' h, fun u a ha h1 => hz u a ha h1, fun u a z => rfl⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeRepresentativesParts_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  first | exact @GlobalTheory.Mem.R3.Tr.reps_parts_tr | exact GlobalTheory.Mem.R3.Tr.reps_parts_tr | (intros; apply GlobalTheory.Mem.R3.Tr.reps_parts_tr <;> assumption)
end

