import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TwAdmProof

theorem not_mem_sq_of_eWL {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : (p : 𝓞 E) ∈ w.asIdeal) (he : eWL E w = 1) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he'
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem not_mem_of_dvd (P : PlE D.host) (he : eWL D.host.E P = 1) {p : ℕ} (hp : p.Prime)
    (h : p ∣ D.host.QS * D.host.q * D.host.d) : (p : 𝓞 D.host.E) ∉ P.asIdeal := fun hv =>
  not_mem_sq_of_eWL hp P hv he (UpperTheory.Ram.mem_sq_of_dvd_condN D.host hp h _ P.isPrime hv)

theorem two_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he Nat.prime_two ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _)

theorem d_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.2.1 (dvd_mul_left _ _)

theorem q_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.1 ((dvd_mul_left _ _).mul_right _)

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem exists_splitK_of (P : PlE D.host) (h1 : P.asIdeal.inertiaDeg ℤ = 1) (he : eWL D.host.E P = 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have hp := GlobalTheory.TwistDet.prime_normV h1
  have hmem : ((Formalism.ConjugateSelfDual.normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2 : Ideal.absNorm P.asIdeal = Formalism.ConjugateSelfDual.normV P := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact h2 ▸ Ideal.absNorm_mem P.asIdeal
  have hodd : Odd (Formalism.ConjugateSelfDual.normV P) := by
    refine hp.eq_two_or_odd'.resolve_left fun e => two_not_mem P he ?_
    rw [e] at hmem; exact hmem
  refine GlobalTheory.TwistDet.exists_splitK h1 he hodd (fun h => q_not_mem P he h) (fun h => d_not_mem P he h)

theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (ψ : Γ →* A) (f : Γ' →* Γ) :
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b ψ).comp f = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ.comp f) := by
  cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.inv_comp]

end GlobalTheory.BigOn.Exp.TwAdmProof

open GlobalTheory.BigOn.Exp.TwAdmProof in

theorem GlobalTheory.BigOn.Exp.twAdm : TwAdm := by
  unfold TwAdm AtTw AtPts
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    EvPt.of_forall fun x hx i p hR _ w hw _ => ?_⟩⟩
  have hmu := (p.tw_iff w).1 hw
  obtain ⟨-, N0, S, hG⟩ := hR.ties.twist
  obtain ⟨-, hall⟩ := hG w hmu
  have h1 := hall 1 (by simp)
  rw [zpow_one] at h1
  have hpsi := h1.1
  refine ⟨?_, ?_, GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ _ (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois w hmu⟩
  · have h2 := Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt ((Fm.ex x hx i).nch.sd w) (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hpsi)
    rw [psiAt_comp, Formalism.MainNotions.psiAt_psiAt] at h2
    exact h2
  · intro P hP
    obtain ⟨-, hin, he⟩ := hpsi.1 P hP
    exact exists_splitK_of P hin he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRow
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem tieRat_of (hA : TwAdm) (hR : RowAt) : TieRat := by
  unfold TieRat AtTw AtPts at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩

end GlobalTheory.BigOn.Exp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariantStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_inner_product_invariant : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  first | exact @GlobalTheory.CovTop.geoUnitary_tied | exact GlobalTheory.CovTop.geoUnitary_tied | (intros; apply GlobalTheory.CovTop.geoUnitary_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull

namespace GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowSum_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → SumOKK := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ t a => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨h1, h2, h3, h4, h5⟩ := GridChoice.sumOK_classes ch.W ch.S.toGridChoice t (ch.Phi a) hL
  obtain ⟨f1, f2, -⟩ := GridChoice.sumOK_flat_fin_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
  obtain ⟨v1, v2⟩ := GlobalTheory.T.gridKernelPairing_independent_of_expansion D T R.toLevCh ch.sc ch.G ch.W Set.univ ch.S.toGridChoice A.μ0 hL t trivial (ch.Phi a)
  exact
    { flat := f1
      flatA := fun w _ => flatIntegrable_aaVac_of_conductor ch.W w (hasConductor_psiAt_AA ch.W w)
      fin := f2
      ex := GridChoice.sumOK_ex hL ch.S.toGridChoice t (ch.Phi a) hde hc
      vec := v1
      indep := v2
      cls := h1
      gam := h2
      wts := h3
      br := h4
      read := h5 }

end GlobalTheory.RowClaim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section RunModelSec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def RunModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp),

    (∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) ∧

    (∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) ∧

    (∃ a : p.P.Gp → C → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp) (c : C)
      (x : Frame M.Ψ D.R.r), x ∈ M.dom →
      ∀ (h1 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ)
        (h2 : M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e (g • c))).Ψ),
        rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀)
            (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (r.lev i g⁻¹) F.1)
            (e c) (castFrame h1 x) =
          (a g c : ℂ) * rdU ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀) F.1 (e (g • c))
            (castFrame h2 (lact (M.tr g c) x))) ∧

    (∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • (M.comp c).L') ∧

    ∃ φ : ∀ c, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
        ((M.comp c).L' ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L'))),
      ∀ (c : C) (u : p.P.Gp), u • c = c → ∃ n : ℤ, ∀ w : (M.comp c).L',
        ∃ hw : Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L',
          Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (M.comp c).L')) ⟨_, hw⟩ =
            φ c ((r.lev i u ^ n) ((φ c).symm (Submodule.Quotient.mk w)))

end RunModelSec

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLargeStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runSizes_quotientGaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) := by
  first | exact @GlobalTheory.RunSizes.gaps_large | exact GlobalTheory.RunSizes.gaps_large | (intros; apply GlobalTheory.RunSizes.gaps_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_function_bound : GlobalTheory.BigTop.Fun.Scale := by
  first | exact @GlobalTheory.BigTop.Fun.existsIntegralMultiple | exact GlobalTheory.BigTop.Fun.existsIntegralMultiple | (intros; apply GlobalTheory.BigTop.Fun.existsIntegralMultiple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamily
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.ShareNumbers

theorem real_bounds (PP TO Dp k f m r nW : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hk : 1 ≤ k) (hD : 1 ≤ Dp) (hr : 1 ≤ r)
    (hPP : (2 * f * m) ^ 4 * nW ≤ PP) (hn40 : 40 ≤ nW) (hnk : k ≤ nW) (hnr : f * r ^ 2 ≤ nW)
    (hTO : PP ^ 4 * Dp ^ 3 * k * f / m ≤ TO) :
    54 * f * r ^ 4 ≤ TO ∧ 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ TO := by
  have hm0 : 0 < m := by linarith
  have hc : 16 ≤ (2 * f * m) ^ 4 := by
    have : 2 ≤ 2 * f * m := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
  have hfm : f * m ≤ (2 * f * m) ^ 4 := by
    have h1 : 1 ≤ 2 * f * m := by nlinarith
    calc f * m ≤ 2 * f * m := by nlinarith
      _ = (2 * f * m) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)
  have hn0 : 0 ≤ nW := by linarith
  have hP640 : 640 ≤ PP := by nlinarith
  have hPm : m * nW ≤ PP := by nlinarith
  have hPfk : f * k ≤ PP := by nlinarith
  have hPfr : f * r ^ 2 ≤ PP := by nlinarith
  have hP0 : 0 ≤ PP := by linarith

  have h4 : PP ^ 3 ≤ PP ^ 4 / m := by
    rw [le_div_iff₀ hm0]
    have : m ≤ PP := by nlinarith
    calc PP ^ 3 * m ≤ PP ^ 3 * PP := by gcongr
      _ = PP ^ 4 := by ring
  have hDkf : 1 ≤ Dp ^ 3 * k * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hk) hf
  have hT : PP ^ 3 * (Dp ^ 3 * k * f) ≤ TO := by
    calc PP ^ 3 * (Dp ^ 3 * k * f) ≤ PP ^ 4 / m * (Dp ^ 3 * k * f) := by gcongr
      _ = PP ^ 4 * Dp ^ 3 * k * f / m := by ring
      _ ≤ TO := hTO
  have hP3 : 0 ≤ PP ^ 3 := by positivity
  constructor
  · have e1 : 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP ^ 3 := by
      have a : 54 * (f * r ^ 2) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * r ^ 2 := by positivity
      calc 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 54 * f * r ^ 4 ≤ 54 * (f * r ^ 2) * (f * r ^ 2) := by
      have : 0 ≤ r ^ 4 := by positivity
      have hff : f ≤ f * f := by nlinarith
      calc 54 * f * r ^ 4 = 54 * r ^ 4 * f := by ring
        _ ≤ 54 * r ^ 4 * (f * f) := by gcongr
        _ = _ := by ring
    calc 54 * f * r ^ 4 ≤ PP ^ 3 := e2.trans e1
      _ = PP ^ 3 * 1 := (mul_one _).symm
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT
  · have e1 : 28 * (f * k) * (f * k) ≤ PP ^ 3 := by
      have a : 28 * (f * k) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * k := by positivity
      calc 28 * (f * k) * (f * k) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by
      have hfk : 0 ≤ (f * k) ^ 3 := by positivity
      have hD2 : Dp * (Dp + 6) ≤ 7 * Dp ^ 3 := by
        have h1 : Dp ≤ Dp ^ 2 := by nlinarith
        have h2 : Dp ^ 2 ≤ Dp ^ 3 := by nlinarith
        nlinarith
      calc 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 4 * (f * k) ^ 3 * (7 * Dp ^ 3) := by gcongr
        _ = 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by ring
    calc _ ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := e2
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT

open Formalism.BasicNotions in

theorem params_bounds {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (p0 : ℕ) (hp : p0 ≤ D.R.r) :
    2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T.TO ∧
      (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / (T.TO : ℝ) ≤
        1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)) := by
  have hf2 : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hDp : T.Dp = D.R.f * (D.R.r * (D.R.r - 1) / 2) := by rw [T.Dp_eq, Nat.choose_two_right]
  have hD1 : 1 ≤ T.Dp := by
    rw [T.Dp_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hnk : D.R.k ≤ T.nWn := by
    have h := T.nW_lo.2.1
    have h' : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnr : D.R.f * D.R.r ^ 2 ≤ T.nWn := by
    have h := T.nW_lo.1
    have h' : D.R.f * D.R.r * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    calc D.R.f * D.R.r ^ 2 = D.R.f * D.R.r * D.R.r := by ring
      _ ≤ _ := h'.trans h
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast hm1
  have hTO : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
    have hn : 0 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f := by
      have : 0 ≤ T.PP ^ 4 := by positivity
      positivity
    have hd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    have hdm : (D.R.m : ℝ) * L.de2 ≤ D.R.m := mul_le_of_le_one_right hm0.le L.thickDensity_le_one
    calc T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m
        ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / ((D.R.m : ℝ) * L.de2) := div_le_div_of_nonneg_left hn hd hdm
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hn hx1) hd.le
  obtain ⟨A, B⟩ := real_bounds T.PP T.TO T.Dp D.R.k D.R.f D.R.m D.R.r T.nWn (by exact_mod_cast hm1)
    (by exact_mod_cast (show 1 ≤ D.R.f by omega)) (by exact_mod_cast hk1) (by exact_mod_cast hD1)
    (by exact_mod_cast (show 1 ≤ D.R.r by omega)) T.PP_nW (by exact_mod_cast T.nW_40) (by exact_mod_cast hnk)
    (by exact_mod_cast hnr) hTO
  constructor
  · have hA : 54 * (D.R.f * D.R.r ^ 4) ≤ T.TO := by
      have : ((54 * (D.R.f * D.R.r ^ 4) : ℕ) : ℝ) ≤ T.TO := by push_cast; linarith
      exact_mod_cast this
    have h1 : p0 * (D.R.r - p0) ≤ D.R.r * D.R.r := Nat.mul_le_mul hp (Nat.sub_le _ _)
    have h2 : 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * (D.R.f * D.R.r ^ 4) := by
      calc 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r)) := by gcongr
        _ = 50 * (D.R.f * D.R.r ^ 4) := by ring
    have h3 : D.R.r ≤ D.R.r ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : 1 ≤ D.R.r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h5 : D.R.r ^ 4 ≤ D.R.f * D.R.r ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [← hDp]
    have hT0 : (0 : ℝ) < T.TO := by
      have : 1 ≤ T.TO := le_trans (by omega) T.TO_40
      exact_mod_cast this
    have hq : (0 : ℝ) < 4 * ((D.R.f : ℝ) * D.R.k) ^ 3 := by
      have : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
      have : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
      positivity
    rw [div_le_div_iff₀ hT0 hq]
    linarith

end GlobalTheory.ShareNumbers

open GlobalTheory.ShareNumbers in

theorem GlobalTheory.ShareNumbers.numbers_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι p0 hp => params_bounds (Fm.parT x hx ι) p0 hp⟩⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsLStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le | exact GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le | (intros; apply GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionEigen
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LagrUniqW

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ l l' : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) → l' ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ ∧ l' (M.co.rho B.ψ u Φ) = l' Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l Φ ∧
        l' (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := by
  intro _hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ l l' hl hl' h0 h1 hne
  obtain ⟨L, hiso, hrank, hL⟩ :=
    GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁
  have hstd : IsStd B.ψ := hP.base.std
  have key : ∀ m : Fn F n d →ₗ[ℂ] ℂ,
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), m (M.co.rho B.ψ u Φ) = m Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        m (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = m Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
        m (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = m φ := by
    intro m hm0 hm1 t w hw φ hφ
    obtain ⟨u, hu, z, hz, heq⟩ := hL t w hw
    rw [heq, hm0 u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ φ hφ), hm1 z hz φ hφ]
  exact GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) L hiso hrank l hl l' hl'
    (key l (fun u hu Φ hΦ => (h0 u hu Φ hΦ).1) (fun z hz Φ hΦ => (h1 z hz Φ hΦ).1))
    (key l' (fun u hu Φ hΦ => (h0 u hu Φ hΦ).2) (fun z hz Φ hΦ => (h1 z hz Φ hΦ).2)) hne

end GlobalTheory.LagrUniqW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartNonzeroIndexPlacesTwistedStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  first | exact @GlobalTheory.BigOn.tupTw_of_w1Row | exact GlobalTheory.BigOn.tupTw_of_w1Row | (intros; apply GlobalTheory.BigOn.tupTw_of_w1Row <;> assumption)
end

