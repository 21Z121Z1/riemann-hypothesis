import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Back

theorem exists_level_vec_in_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → (R.toCx3 F).PartsW false → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  obtain ⟨w, hw, hw0, hws⟩ := GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span R F hCW hEx hSch s hOk hGG hLU j c h0
  exact ⟨w, hw, hw0, GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms R F hParts j w hws⟩

theorem blockProd_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold BlockDat.blockProd
  rw [ne_eq, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  intro ν _ h
  unfold Formalism.L2.Col.blockPoly at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨c, _, hc⟩ := h
  have := congrArg (fun q => Polynomial.coeff q 0) hc
  simp at this

theorem eig_in_sum {H : Type} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H] {Q J K : Type} (ok : Q → Prop)
    (h : Q → J → Module.End ℂ H) (ev : K → Q → J → ℂ) (V : K → Submodule ℂ H) (S : K → Prop) (k0 : K)
    (hc : ∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c'))
    (hev : ∀ k P, ok P → ∀ cc, ∀ x ∈ V k, h P cc x = ev k P cc • x)
    (w : H) (hw : w ∈ V k0) (hw0 : w ≠ 0) (hwS : w ∈ ⨆ (k : K) (_ : S k), V k) :
    ∃ k, S k ∧ ∀ P, ok P → ∀ cc, ev k P cc = ev k0 P cc := by
  classical
  let op : {P // ok P} × J → Module.End ℂ H := fun i => h i.1.1 i.2
  have hpc : Formalism.L2.Col.PairComm op := fun i i' => hc _ _ i.1.2 i'.1.2 _ _
  let χ : K → {P // ok P} × J → ℂ := fun k i => ev k i.1.1 i.2
  have hV : ∀ k, V k ≤ Formalism.L2.Col.eigAt op (χ k) := fun k x hx =>
    Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hev k i.1.1 i.1.2 i.2 x hx
  by_contra hne
  push_neg at hne
  have h1 : (⨆ (k : K) (_ : S k), V k) ≤ Formalism.L2.Col.eigSum op (fun x => x ≠ χ k0) := by
    refine iSup₂_le fun k hk => (hV k).trans (Formalism.L2.Col.eigAt_le_eigSum ?_)
    intro he
    obtain ⟨P, hP, cc, hcc⟩ := hne k hk
    exact hcc (congrFun he (⟨P, hP⟩, cc))
  have h2 : V k0 ≤ Formalism.L2.Col.eigSum op (fun x => x = χ k0) :=
    (hV k0).trans (Formalism.L2.Col.eigAt_le_eigSum rfl)
  have hd := Formalism.L2.Col.disjoint_eigSum (op := op) hpc (C := fun x => x = χ k0) (C' := fun x => x ≠ χ k0)
    (fun x h h' => h' h)
  exact hw0 ((Submodule.disjoint_def.1 hd) w (h2 hw) (h1 hwS))

theorem types_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (hSep : A3.fam3.TypesSep3) (j : Fin D.R.m)
    (p p' : A3.fam3.base3.Ix) (y : (A3.liftI j A3.A.μ0).OpIx → ℂ)
    (hp : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) y)
    (hp' : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p'.1)) y) : p = p' := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', hxx⟩ := hp'
  have hxe : x = x' := funext fun i => D.what₂.embLL.injective (congrFun hxx i)
  subst hxe
  by_contra hne
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  rcases hSep p.1 p.2 p'.1 p'.2 hne' j with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have h1 := hx.1 P
    have h2 := hx'.1 P
    rw [h1] at h2
    exact mul_right_cancel₀ (blockProd_ne_zero _ P) h2
  · exact hk ((hx.2 k).symm.trans (hx'.2 k))

theorem wc_le_wp_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr hParts hSep j pl cV cW hLD p c hsys
  obtain ⟨hcoreF, hSF, -, -, -, hWeq, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hCW
  have hcore := hcoreF hEx
  obtain ⟨h, -, hNorm, -, hsum, -, hev, hchar⟩ :=
    GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hSch hOk.ok2.irr R.SF hSF j
  have hidem := (eH_laws R.toRealDat F.lv2 hcore hOk.ok2.irr j).1
  by_cases h0 : R.Wc' j c = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨w, hwc, hw0, hwp⟩ := exists_level_vec_in_parts R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  have hwp' : w ∈ ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
    have hle : (⨆ p, R.Wp3 j p) ≤
        ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
      refine iSup_le fun p' => iSup₂_le fun c' hc' => ?_
      rw [hWeq]
      exact le_iSup₂_of_le (f := fun c' (_ : ∃ p', R.Carries p' c') => Wcc R.toRealDat R.SF j c') c' ⟨p', hc'⟩ le_rfl
    exact hle hwp
  rw [hWeq] at hwc
  obtain ⟨c', ⟨p', hcar⟩, hag⟩ := eig_in_sum (Good R.toRealDat A3.A.μ0) h
    (fun c P cc => evC (Wc D j) P (c P) cc) (Wcc R.toRealDat R.SF j) (fun c' => ∃ p', R.Carries p' c') c hNorm.1
    (fun k P hP cc x hx => hev k P hP cc x hx) w hwc hw0 hwp'
  have hsub : Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro x hx
    refine hchar c' x ?_ ?_
    · have hr : x ∈ LinearMap.range (eH R.toRealDat j) := hsum ▸ (le_iSup (Wcc R.toRealDat R.SF j) c hx)
      obtain ⟨y, rfl⟩ := hr
      rw [← Module.End.mul_apply, hidem]
    · intro P d hP hd
      rw [hev c P hP _ x hx, ← hag P hP]
      simp [evC, hd]
  have hne : R.Wc' j c' ≠ ⊥ := by
    rw [hWeq]
    intro hb
    exact hw0 ((Submodule.eq_bot_iff _).1 hb w (hsub hwc))
  have hfwd := GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr j pl cV cW hLD p' c' hcar hne
  have hlab : labW j pl cW c' = labW j pl cW c := funext fun i => hag (pl i) (hLD.good i) (cW i)
  rw [hlab] at hfwd
  have hpp : p' = p := types_eq hSep j p' p _ hfwd hsys
  subst hpp
  rw [hWeq]
  refine hsub.trans ?_
  rw [← hWeq]
  exact le_iSup₂_of_le (f := fun c (_ : R.Carries p' c) => R.Wc' j c) c' hcar le_rfl

end GlobalTheory.Hk3.Back
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusSemisimplificationWeilDeligneRestrictsStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSemisimplification_weilDeligne_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  first | exact @GlobalTheory.AboveL.restricts_of_isFrobSS | exact GlobalTheory.AboveL.restricts_of_isFrobSS | (intros; apply GlobalTheory.AboveL.restricts_of_isFrobSS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepOfPolarizedPairOfHyps
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.GalBridge

theorem galoisRepOfPolarizedPair_of_polarizedGaloisRep :
    LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → IrreducibleAdmissibleGL →
      StandardFunctorsFiniteLength → PolarizedGaloisRepPublished → GaloisRepOfPolarizedPair := by
  intro h1 h2 h3 h4 h5 H
  have hU : RecUnique := GlobalTheory.T.reciprocity_unique_of h1 h2 h3 h4 h5
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp
  obtain ⟨r, wt, HT, P⟩ := H E Ω l ι a ha π χ hr hp
  obtain ⟨n, hn⟩ := GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair E a ha π χ hr hp
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨art, hart, hL⟩ :=
    (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1
      (maximalRealSubfield E) Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hL l ι χ n hn
  have hμ' : IsLAdicCharOf ι χ μ := ⟨hμc, art, n, hart, hn, hμ⟩
  have hcont : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) :=
    Units.continuous_val.comp P.cont
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := by
    intro τ u o
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  refine ⟨r, wt, HT, ?_⟩
  exact
    { cont := P.cont
      ss := P.ss
      pol := ⟨μ, hμ', P.pol μ hμ'⟩
      away := fun w hl A h rc hrc σ hσ => by
        rw [← P.away w hl A h rc (hU.isTheRec_of_isRec hrc) σ hσ]
        exact isWDOf_wdOf (h := h) hl ι hcont
      pure := fun w hl A h => ⟨wdOf h hl ι r, isWDOf_wdOf (h := h) hl ι hcont, P.pure w hl A h⟩
      weights := fun τ => P.weights τ _ (hasInfChar_infChar_of_commute E a hcap (CG.mk π) (ι.toRingHom.comp τ))
      weights_conj := P.weights_conj
      above := fun Pr AI hT w A h O _ _ _ Bw hj =>
        let Q := P.above Pr AI hT w A h O Bw hj
        { deRham := Q.deRham
          jumps := Q.jumps
          iwahori := fun σ hσ hI =>
            ⟨(Q.iwahori σ hσ hI).1, fun rc hrc => (Q.iwahori σ hσ hI).2 rc (hU.isTheRec_of_isRec hrc)⟩
          crys := Q.crys } }

end GlobalTheory.GalBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSpecHomSpecMapAppTop
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped NumberField
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.FiberCard

theorem isoSpec_hom_specMap_appTop' {P : Scheme.{0}} [IsAffine P] {R : CommRingCat.{0}} (s : P ⟶ Spec R) :
    P.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appTop) = s := by
  rw [Scheme.isoSpec_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end GlobalTheory.IwLevel.FiberCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLawsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rep_of_reading_laws : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → Laws S → ∀ i, RepOfLoc D.nd D.naut i := by
  first | exact @GlobalTheory.RepOfLocal.main | exact GlobalTheory.RepOfLocal.main | (intros; apply GlobalTheory.RepOfLocal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.Published

namespace GlobalTheory.QuadLiftBridge

theorem quadLift : ArthurClozelStrongTC → JacquetShalikaRigidity → GlobalTheory.GalCut.QuadLift := by
  intro hAC hJS K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hw, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  refine hAC K M (h2 ▸ Nat.prime_two) a ha π fun η hη hST => ?_
  have hsm : CG.mk π = (CG.mk π).twist η := by
    refine JacquetShalikaRigidity.strong_multiplicity_one hJS ha _ _ (hST.mono fun v ⟨hu, B', h1, h3⟩ => ⟨B', h1, ?_⟩)
    have := h1.twist hu
    rwa [h3] at this
  exact GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha (CG.mk π) η _ B hB (GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime K M h2 η hη w hw) hsm.symm

end GlobalTheory.QuadLiftBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrOfConjRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.RealGal.ConjUnr

theorem unr_of_conj_res : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)), UpperTheory.V.Af.RepIso r (ρ.comp (UpperTheory.V.Af.Bc.res E Ω ↥Q.K)) → (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := ↥Q.K) A, r s = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1 := by
  intro E Ω _ _ _ _ _ Q l _ a ρ r hiso hr
  haveI : FiniteDimensional E Q.K := Module.finite_of_finrank_eq_succ Q.two
  have hS1 := GlobalTheory.InertiaAlmostAll.finite_ramified E Ω Q.K
  have hbad := Filter.eventually_cofinite.mp hr
  have hS2 := hbad.image (fun u : HeightOneSpectrum (𝓞 ↥Q.K) => u.under (𝓞 E))
  refine Filter.eventually_cofinite.mpr ((hS1.union hS2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨A, hA, s, hs, hρ⟩ := hw
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image, not_or, not_exists, not_and] at hn
  obtain ⟨h1, h2⟩ := hn
  have hfix : s ∈ Q.K.fixingSubgroup := by
    by_contra hns
    exact h1 A hA (fun hle => hns (hle hs))
  obtain ⟨u, hu⟩ := GlobalTheory.LocLanglands.EpsUnique.exists_place hA ↥Q.K
  have hwu : u.under (𝓞 E) = w := ReciprocityTheory.Gal.eq_of_isPlaceOver (GlobalTheory.DelGlob.placeUnder_isPlaceOver ↥Q.K hu) hA
  have hgood : ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ t ∈ Ine (F := ↥Q.K) A, r t = 1 := by
    by_contra hb
    exact h2 u hb hwu
  let t : G ↥Q.K Ω := IntermediateField.fixingSubgroupEquiv Q.K ⟨s, hfix⟩
  have hts : UpperTheory.V.Af.Bc.res E Ω ↥Q.K t = s := AlgEquiv.ext fun _ => rfl
  have ht : t ∈ Ine (F := ↥Q.K) A := ⟨hs.1, hs.2⟩
  obtain ⟨g, hg⟩ := hiso
  apply hρ
  have := hg t
  rw [MonoidHom.comp_apply, hts, hgood A hu t ht] at this
  rw [this]; simp

end GlobalTheory.RealGal.ConjUnr
end

