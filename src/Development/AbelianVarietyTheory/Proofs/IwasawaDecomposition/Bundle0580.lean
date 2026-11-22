import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsEnl
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

set_option maxHeartbeats 4000000 in

theorem exists_omPins_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev ∧
          IsBCOf (O' i') (v₀' i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) (z.geo.O i)
            (z.geo.v₀ i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z.geo.κ i) (iotaW z.core i)
            (z.core.x₀ ((i : ℕ) + 1) (z.geo.O i).s0)
            (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
              (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  have hc := GlobalTheory.T.exists_coefficientMap_extension_over_enlarged_base z hE hf hp hS R' cG' hP hL hB hW
  have a1 : HEq R'.C.mu0 f'.mu0 ∧ HEq R'.C.eta f'.eta := by
    have e := hL.C
    rw [w'.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  have a2 : HEq z.R.C.mu0 f.mu0 ∧ HEq z.R.C.eta f.eta := by
    have e := z.lev.C
    rw [w.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  obtain ⟨-, -, eβW, -, -, -, eβV, -, -, ePg, eG, -, hcV, -⟩ := hW
  have hcV' := fun i i' hi => (⟨(hcV i i' hi).1, (hcV i i' hi).2.2.1, (hcV i i' hi).2.2.2.1⟩ : _ ∧ _ ∧ _)
  have h1 := hP.char.base.lev
  have h2 := hP.char.base.models
  have h3 := hP.char.base.fam.tie
  clear hcV hP hL hB hS
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have key := fun i => exists_bc_stages (w.st Z) _ ((by with_unfolding_all exact ((Eq.refl B.toPre) :))) hLL z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ex eι
    ePg eβV eβW eG (a1.1.trans a2.1.symm) (a1.2.trans a2.2.symm) z.pins.char.base.lev z.pins.char.base.models.HV z.geo.fw.kap h1 h2 h3 ht
    i i rfl (hcV' i i rfl).1 (hcV' i i rfl).2.1 (hcV' i i rfl).2.2 (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2 _ (hc i i rfl)
  choose O' k1 k2 k3 using key
  refine ⟨(by with_unfolding_all exact (O' :)), fun i => (by with_unfolding_all exact ((And.intro (k1 i) (k2 i)) :)), fun i i' hi => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  exact (by with_unfolding_all exact ((And.intro (k3 i).lev (k3 i)) :))

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeCharts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.Mem.Top.KerTwLv

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stepBasis_std : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  intro K B f T w hK hF hP Z t Wt nch n Y hmu hQp O hstdO hunf E hent Fl hfl hwt u v hg hμ tt hstd j hj
  have hsc := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 (j+1) hj
  obtain ⟨k, hk⟩ := hstd.1.reads u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  have hcar := tt.forms.car u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  refine ⟨1, ?_, ?_⟩
  · rw [hsc.1]
    simp [cT, Matrix.map_one]
  · intro β w' h x
    have hfr : GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg (1 : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E) w' h = 1 :=
      map_one _
    rw [hfr, inv_one]
    simp only [Units.val_one, Matrix.one_mulVec]
    have hT : ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
      intro hT
      have hcop : Nat.Coprime ((w.D Z).what₂.places.resChar v) ((w.D Z).mem u).A.T :=
        (Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      apply w'.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((1 : ℤ) : 𝓞 (w.D Z).host.F) = (a : 𝓞 (w.D Z).host.F) * (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F)
          + (b : 𝓞 (w.D Z).host.F) * ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) := by
        rw [← hab]; push_cast; ring
      rw [Int.cast_one] at e
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hT)
    have hLb : ∀ y, y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
        ∀ a, ∃ r : 𝓞 (w.D Z).host.E, y a = r ∧ (a.1 + 1 = ((w.D Z).sp.X (j + 1)).rank → (w.px.piT u : 𝓞 (w.D Z).host.E) ∣ r) := by
      intro y
      have e1 := (hcar β).Lb_eq
      have e2 := hk.lb β
      have hr := rankN (w.D Z) (j + 1) hj
      have hmap : y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
          reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E y ∈
            reL (rankN (w.D Z) (j + 1) hj) (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb := by
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := (reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E).injective hzy
          exact this ▸ hz
      rw [hmap, ← e1]
      refine (e2 _).trans ?_
      simp only [TC.baseL, Set.mem_setOf_eq, reV, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      constructor
      · intro H a
        obtain ⟨r, hr1, hr2⟩ := H (finCongr hr a)
        refine ⟨r, ?_, fun ha => hr2 ?_⟩
        · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply] at hr1
          exact hr1
        · have e : ((finCongr hr a : Fin _) : ℕ) = a := rfl
          rw [e]
          exact ha.trans hr
      · intro H b
        obtain ⟨r, hr1, hr2⟩ := H ((finCongr hr).symm b)
        refine ⟨r, hr1, fun hb => hr2 ?_⟩
        have e : (((finCongr hr).symm b : Fin _) : ℕ) = b := rfl
        rw [e]
        exact hb.trans hr.symm
    have hπ : (w.px.piT u : 𝓞 (w.D Z).host.E) * (B.fields.conjO (w.px.piT u) : 𝓞 (w.D Z).host.E) =
        ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.E) :=
      B.primes_piT_norm w.px u
    have L := @GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ _ w' _ _ _ _ _ _ hT hπ hLb
    have PI := @GlobalTheory.T.splitting_fst_mem_integers' (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ w' _ ((t.g.herm.g u v hg).spl_alg w' h)
    constructor
    · rintro ⟨y, hy, hyx⟩ a
      rw [← hyx a]
      exact PI _ ((L y).1 hy a)
    · intro hx
      refine ⟨fun a => (1 : (w.D Z).host.E) ⊗ₜ[(w.D Z).host.F] x a, (L _).2
        (fun a => Subring.subset_closure (Or.inr ⟨⟨x a, hx a⟩, rfl⟩)), fun a => ?_⟩
      rw [(t.g.herm.g u v hg).spl_alg]

end GlobalTheory.Mem.Top.KerTwLv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriod
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.CuspFrom.PeriodTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}

theorem exists_isExp_of_sabMap {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} (B : GlobalTheory.CM.PAT H (Sp ℂ))
    (m : SABMap B.t t y) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hP : IsPeriod D ty P)
    (hol : IsHolTo Set.univ fun z => (e z).left) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ P.range) (lin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    ∃ ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G), GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) y hy
  have hp' : ∀ z, (p.symm (e z)).left ≫ m.φ = (e z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => p.symm (e z), hP, ?_, fun z w => ?_, p.symm.surjective.comp onto, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · refine ThetaPoint.isHolTo_fibre m.cart.1 _ (fun z => (Over.w (p.symm (e z))).trans hid) ?_
    have h : (fun z => (p.symm (e z)).left ≫ m.cm.F) = fun z => (e z).left := funext hp'
    exact h ▸ hol
  · beta_reduce
    rw [add, map_mul]
  · exact (map_eq_one_iff _ p.symm.injective).trans (ker z)
  · beta_reduce
    rw [lin, p.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
    exact congrArg (· ≫ _) (hp' z).symm
  · exact (GlobalTheory.CM.ExCompare.weilIs_iff m _ _ hy k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (weil k a b c hk hc)

theorem exists_isExp_of_rank_zero (l : Level H) (hD : D.p + D.q = 0) (hP : IsPeriod D ty P) :
    ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)),
      GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  obtain ⟨B, hB, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H D l _ _ _ _
    (Models.RankZero.zeroObj hD l (spMap (algebraMap (KA l) ℂ)))
  have hz : IsIso B.t.G.hom := by
    rw [hB]
    exact Models.RankZero.isIso_zeroTriple _
  have := Models.RankZero.subsingleton_La hD
  have h0 : ∀ z : Fin g → ℂ, z = 0 := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1 ▸ Submodule.mem_top
    refine (Submodule.span_le (p := ⊥)).2 ?_ hz
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨B, fun _ => 1, hP, fun U f => ⟨?_, differentiableOn_const _⟩, fun _ _ => (_root_.mul_one _).symm,
    fun x => ⟨0, Models.RankZero.hom_unique hz _ _⟩, fun z => ⟨fun _ => ⟨0, by rw [map_zero, h0 z]⟩, fun _ => rfl⟩,
    fun _ _ => Models.RankZero.hom_unique hz _ _, fun k a b c hk hc => ?_⟩
  · simp only [Set.mem_univ, true_and]
    exact isOpen_const
  · have e : c = 1 := Units.ext (by rw [hc, Subsingleton.elim b 0, map_zero]; simp)
    rw [e, unitOn, map_one]
    exact Models.RankZero.weilIs_zero hz B.t.PP.isLB (Models.RankZero.triv_rig hz _) _ _ _

end GlobalTheory.CuspFrom.PeriodTriple

namespace GlobalTheory.CuspFrom

theorem exists_pat_isExp_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  intro E _ _ _ H l₀ DB g ty PB hty hP
  rcases Nat.eq_zero_or_pos (DB.p + DB.q) with h0 | hpq
  · exact PeriodTriple.exists_isExp_of_rank_zero l₀ h0 hP
  have kn := known_holds
  obtain ⟨l, hA⟩ : ∃ l : Level H, l.A = 1 := ⟨{ l₀ with A := 1, A_pos := one_pos }, rfl⟩
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, -, -, ⟨add, onto, hol, -⟩, ker, lin, weil, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws
    E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty DB LinearMap.id PB
    ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨U, hU, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H DB l _ _ _ _ Xo.univ
  obtain ⟨B, m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ y U
  exact ⟨B, PeriodTriple.exists_isExp_of_sabMap B (hU ▸ m) e hP hol add onto ker lin weil⟩

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem card_frame_index {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h6 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at h6
  simp_rw [Fintype.card_fin, Datum.mult] at h6
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul] at h6
  rw [h6, mul_add]

theorem exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  intro E _ _ _ H Dw l Xo c g e S _ _ _ y hpq
  obtain ⟨U, hU, hg⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hgp : 1 ≤ T.g := by
    rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  obtain rfl : T.g = g := hTg.trans (hg.trans (card_frame_index Dw e))
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m
  obtain ⟨th, ht⟩ := h₁ y.s
  have hne := (h₂ th _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis
  obtain ⟨hl, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart
  choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)
  refine ⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩
  rw [funext hv]
  exact hB

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.DiscrDvd

theorem irreducible_X_sub_X {σ : Type} {a b : σ} (h : a ≠ b) :
    Irreducible (X a - X b : MvPolynomial σ ℝ) := by
  classical
  have hc : coeff (Finsupp.single a 1) (X a - X b : MvPolynomial σ ℝ) = 1 := by
    have : ¬ (Finsupp.single b 1 = Finsupp.single a 1) := fun e =>
      h (Finsupp.single_left_injective one_ne_zero e).symm
    simp [coeff_X, this]
  refine irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx => ?_
  · exact (totalDegree_sub _ _).trans (by simp)
  · have := le_totalDegree (p := (X a - X b : MvPolynomial σ ℝ)) (s := Finsupp.single a 1)
      (by rw [mem_support_iff, hc]; exact one_ne_zero)
    simpa using this
  · exact isUnit_of_dvd_one (hc ▸ hx _)

theorem isRelPrime_X_sub_X {σ : Type} {a b c d : σ} (h : a ≠ b) (h' : c ≠ d)
    (hn : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b)) :
    IsRelPrime (X a - X b : MvPolynomial σ ℝ) (X c - X d) := by
  classical
  refine (irreducible_X_sub_X h).isRelPrime_iff_not_dvd.2 fun hd => ?_
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := map_dvd (eval (Pi.single c (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'.symm] at this
  · have := map_dvd (eval (Pi.single d (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'] at this

theorem rootDiscr_dvd (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ)
    (hP : ∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) :
    GoodMetric.rootDiscr m ∣ P := by
  classical
  have ne : ∀ (τ : ι) (i j : Fin (m τ)), i ≠ j → (⟨τ, i⟩ : Root m) ≠ ⟨τ, j⟩ := fun τ i j h e =>
    h (eq_of_heq (Sigma.mk.inj e).2)
  unfold GoodMetric.rootDiscr
  refine Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ hτ => ?_) fun τ _ => ?_
  · refine IsRelPrime.prod_left fun j _ => IsRelPrime.prod_left fun i hi =>
      IsRelPrime.prod_right fun l _ => IsRelPrime.prod_right fun k hk => ?_
    refine isRelPrime_X_sub_X (ne _ _ _ (Finset.mem_Iio.1 hi).ne') (ne _ _ _ (Finset.mem_Iio.1 hk).ne')
      (Or.inl ⟨fun e => hτ (Sigma.mk.inj e).1.symm, fun e => hτ (Sigma.mk.inj e).1.symm⟩)
  refine Finset.prod_dvd_of_isRelPrime (fun j _ l _ hjl => ?_) fun j _ => ?_
  · refine IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun k hk => ?_
    have hi := Finset.mem_Iio.1 hi
    have hk := Finset.mem_Iio.1 hk
    rcases lt_or_gt_of_ne hjl with h | h
    · exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hi.trans h).ne'⟩)
    · exact (isRelPrime_X_sub_X (ne _ _ _ hk.ne') (ne _ _ _ hi.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hk.trans h).ne'⟩)).symm
  refine Finset.prod_dvd_of_isRelPrime (fun i hi k hk hik => ?_) fun i hi => hP τ i j (Finset.mem_Iio.1 hi)
  have hi := Finset.mem_Iio.1 hi
  have hk := Finset.mem_Iio.1 hk
  exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
    (Or.inr ⟨ne _ _ _ hk.ne, ne _ _ _ hik.symm⟩)

end GlobalTheory.GoodMetric.DiscrDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.RootDiscrPerm

theorem prod_Iio_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i)) = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

theorem det_vandermonde_comp_perm {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    (Matrix.vandermonde (fun i => v (σ i))).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

theorem rootDiscr_eq_prod_det (ι : Type) [Fintype ι] (m : ι → ℕ) :
    rootDiscr m = ∏ τ, (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
  unfold rootDiscr
  exact Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _

end GlobalTheory.GoodMetric.RootDiscrPerm

open GlobalTheory.GoodMetric.RootDiscrPerm in
theorem GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  intro ι _ m w
  rw [rootDiscr_eq_prod_det, map_prod]
  have h : ∀ τ, rename (Equiv.sigmaCongrRight w)
      (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det =
      ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    have e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix
        (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) =
        Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ)) := by
      ext i k; simp [Matrix.vandermonde_apply]
    rw [e]
    exact det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)
  rw [Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]
  push_cast
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  first | exact @GlobalTheory.InertiaFix.sigma_fixes_abelianPart | exact GlobalTheory.InertiaFix.sigma_fixes_abelianPart | (intros; apply GlobalTheory.InertiaFix.sigma_fixes_abelianPart <;> assumption)
end

