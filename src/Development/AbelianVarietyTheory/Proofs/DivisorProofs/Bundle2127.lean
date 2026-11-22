import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugate
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmARatio

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host

theorem twisted_value {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (𝓞 E))} {χ ξ : HChar E}
    {Λ : ℂ → ℂ} {m : ℕ} (hU : UnramFin E) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q))
    (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hm : m ≠ 0) (hord : ξ.OrderDvd m) (htr : TrivOnF ξ) (htame : ∀ v, ξ.TameAt v)
    (hram : ∀ v, ξ.UnrAt v ↔ v ∉ Q) (hΛ : IsHeckeL (χ * ξ) Λ) :
    ∃ (ψc : PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) (T : (PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) → ℂ),
      (∀ y, finPart ξ y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 (belowSet Q)) χ ψ (T ψ)) ∧ Λ s = T ψc := by
  classical
  have hp : ∀ x, ξ.1 x ^ m = 1 := fun x => by
    have := congrArg (fun c : HChar E => c.1 x) hord
    simpa using this
  have hχu : ∀ v ∈ belowSet Q, ∀ P, Over P v → χ.UnrAt P := fun v hv P hP => by
    have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rwa [expIn, multiplicity_eq_zero.2 (hQ v hv).2, expAt_zero_iff] at e
  have hξu : ∀ v ∉ belowSet Q, ∀ P, Over P v → ξ.UnrAt P := fun v hv P hP =>
    (hram P).2 fun h => hv (Finset.mem_image.2 ⟨P, h, HeightOneSpectrum.ext hP⟩)
  have hv : IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
    refine ⟨hχ.1.mul (GlobalTheory.ToricDistribution.isUnitary_of_pow hm hp), hχ.2.1.mul htr, fun k => ?_,
      fun v P hP => ⟨fun hv => ?_, fun hv n => ?_⟩⟩
    · rw [HChar.inf_mul, GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one]
      exact hχ.2.2.1 k
    · intro x hx hx1
      rw [HChar.loc_mul, hχu v hv P hP x hx, htame P x hx hx1, one_mul]
    · rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) n]
      refine forall_congr' fun x => forall_congr' fun hx => ?_
      rw [HChar.loc_mul, hξu v hv P hP x hx, mul_one]
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have hex : ∀ q : HeightOneSpectrum (OF E), ∃ P, q ∈ belowSet Q → P ∈ Q ∧ Over P q := fun q => by
    by_cases e : q ∈ belowSet Q
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 e
      exact ⟨P, fun _ => ⟨hP, over_below P⟩⟩
    · exact ⟨P₀, fun h => absurd h e⟩
  choose Pq hPq using hex
  have t := GlobalTheory.ToricDistributionObj.toricSumFormula_holds E I φ hφ s κ 𝔣 (belowSet Q) (χ * ξ) Pq Λ hU hs hb hQ hv
    (fun q hq => (hPq q hq).2) hΛ
  rw [Finset.filter_false_of_mem, Finset.prod_empty, mul_one] at t
  swap
  · intro q hq h
    refine (hram (Pq q)).1 (fun x hx => ?_) (hPq q hq).1
    have := h x hx
    rwa [HChar.loc_mul, hχu q hq _ (hPq q hq).2 x hx, one_mul] at this
  have hker : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ (finPart ξ).ker := by
    refine sup_le ?_ fun y hy => ?_
    · rintro _ ⟨k, rfl⟩
      have := finPart_mul_inf ξ k
      rwa [GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one] at this
    · refine GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level htr (fun v => ?_) hy
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P _ => htame P⟩
        rw [pow_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
      · exact ⟨0, by rw [pow_zero]; exact one_dvd _, fun P hP => (ξ.unrAt_iff P).1 (hξu v hv P hP)⟩
  have hψ : ∀ y, finPart ξ y = QuotientGroup.lift _ (finPart ξ) hker (QuotientGroup.mk y) := fun _ => rfl
  obtain ⟨hfin, S, hS, hT⟩ := (isTwistedSum_iff_isToricSum hψ _).2 t
  exact ⟨_, fun ψ => ∑ᶠ q : PicO (condQ 𝔣 (belowSet Q)), ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0, hψ,
    fun ψ => ⟨hfin, S, hS, rfl⟩, hT⟩

theorem dvd_cond0 {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (v : HeightOneSpectrum (OF D.host.E))
    (h : v.asIdeal ∣ GlobalTheory.FunObj.SqNum.condF P) : v.asIdeal ∣ GlobalTheory.LamTie.cond0 D.host (P.w P.v0) := by
  obtain ⟨u, hu, hd⟩ := (v.prime.dvd_finset_prod_iff _).1 h
  have e : v = u := HeightOneSpectrum.ext
    (associated_iff_eq.1 ((v.irreducible.dvd_irreducible_iff_associated u.irreducible).1 (v.prime.dvd_of_dvd_pow hd)))
  subst e
  rcases P.mem_S0_of_sum_eq.1 hu with h0 | h1
  · have e : below (P.w P.v0) = v := (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))).trans h0.symm
    unfold GlobalTheory.LamTie.cond0
    rw [e]
    exact dvd_mul_left _ _
  · refine Dvd.dvd.mul_right (Dvd.dvd.pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    push_cast
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1 with h | h | h | h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.ThmARatio

theorem GlobalTheory.ThmARatio.values_as_toric_sums : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit _ hF hTor w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨_, _, hfd, hb, -⟩ := hF
  have hχ : fam d.G p.P.A3.A.μ0 i j (some (decide (D.what₂.places.resChar w = D.host.pde))) =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    unfold fam GlobalTheory.FunObj.SqNum.delOf Formalism.L2.Host.CharFrame.delAt
    by_cases h : D.what₂.places.resChar w = D.host.pde
    · simp only [h, decide_true, cond_true, if_true]
    · simp only [h, decide_false, cond_false, if_false]
  obtain ⟨T₀, ⟨hv, h0⟩, hne, hL, -⟩ := hTor i j s hs1 hs2 (some (decide (D.what₂.places.resChar w = D.host.pde)))
  rw [hχ] at hv h0 hL
  have hP := p.Tp.psi_is w hw
  obtain ⟨a, ha⟩ := hP.ord
  have hQ := (GlobalTheory.ToricDenom.placesBelow_splitCoprimeConductor_of_admissible (hfit.1.cond w hw) (𝔣 := GlobalTheory.FunObj.SqNum.condF d.G.pl) fun P h =>
    (hfit.1.list _ (hfit.1.setting.inW1 hw)).1 P (GlobalTheory.ThmARatio.dvd_cond0 d.G.pl _ h)).1
  obtain ⟨ψc, T, h1, h2, h3⟩ := GlobalTheory.ThmARatio.twisted_value hfd.2.2.2.2.2.2.1 hfd.2.2.1 hs1 hb hQ hv
    (pow_ne_zero a (D.what₂.places.resChar_prime w).ne_zero) ha hP.triv hP.tame hP.ram hΛ
  exact ⟨T₀, ψc, T, hv, h0, hne, (hL Λd hΛd).symm, h1, h2, h3⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMember
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMoveSnd

variable {D : D7}

theorem heisO_smul' {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    (a : ℂ) {g₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c g₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (a • g₀) (a • Tm) :=
  { trans := fun Φ hΦ x hx => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul']
    modul := fun Φ hΦ y hy => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul']
    vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem isThetaAt_rescale {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c κ : ℂ}
    {f₀ Φ f : WO S T → ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (κ • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  refine ⟨⟨κ⁻¹ • Tm, ?_⟩, fun Tm' hT' => ?_⟩
  · have := isPlaceModel_smul κ⁻¹ hT
    rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  · rw [hall _ (isPlaceModel_smul κ hT'), LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem isHalf_iff_smul {m n : ℕ} (c : AE D) (u : Mx D m n) : IsHalf c u ↔ c • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem isHalf_actO' {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf c x) :
    IsHalf c (actO S T g h x) := by
  rw [isHalf_iff_smul] at hx ⊢
  rw [GlobalTheory.VacMove.actO_eq]
  conv_rhs => rw [← hx]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_actO_inv_iff {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf c (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf c x := by
  refine ⟨fun hx => ?_, isHalf_actO' c _ _⟩
  have := isHalf_actO' c g h hx
  have e := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) g⁻¹ h⁻¹ x
  simp only [inv_inv] at e
  rwa [e] at this

theorem frame_move_alg {R : Type} [CommRing R] {s t : ℕ} (a βS : GL (Fin s) R) (b βT : GL (Fin t) R)
    (K : Matrix (Fin s) (Fin t) R) :
    ((a * βS)⁻¹ : GL (Fin s) R).1 * K * (b * βT).1 =
      (βS⁻¹).1 * (a⁻¹).1 * βS.1 * ((βS⁻¹).1 * K * βT.1) * ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R).1 := by
  have e1 : (βS.1 : Matrix (Fin s) (Fin s) R) * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : (βT.1 : Matrix (Fin t) (Fin t) R) * (βT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e3 : ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R) = βT⁻¹ * b * βT := by group
  rw [e3, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1 (βS⁻¹).1, e1, Matrix.one_mul, ← Matrix.mul_assoc βT.1 (βT⁻¹).1, e2, Matrix.one_mul]

theorem frMapAdj_move (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D S)
    (h : GA D T) (x : WO S T) :
    frMapAdj S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapAdj S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have split : actO S T g⁻¹ h⁻¹ x = actO S T g⁻¹ 1 (actO S T 1 h⁻¹ x) := by
    simp only [GlobalTheory.VacMove.actO_eq, inv_one, GlobalTheory.VacMove.mt_one₀, Matrix.one_mul, Matrix.mul_one]
  rw [split, GlobalTheory.FreeBlockTwist.frMapAdj_actO_one, GlobalTheory.AdjAct.frMapAdj_actO, ← GlobalTheory.AdjAct.finE_inv_val, ← map_inv]
  unfold frMapAdj
  rw [map_inv (Lev.finE S), map_inv (Lev.finE T), ← Matrix.mul_assoc]
  exact frame_move_alg (R := EAf D) (Lev.finE S g) βS (Lev.finE T h) βT _

theorem stdSnd_move (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    stdSnd ν e I a S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = stdSnd ν e I a S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  unfold stdSnd dualCoord
  rw [frMapAdj_move]
  rw [propext (isHalf_actO_inv_iff (cA D e) g h x)]

theorem snd_moved : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv' t
  have hWe : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := (GlobalTheory.Grid.isWeil_false ψ A' WW _ _ _).1 (hY.weil' t)
  have hee : cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self (hY.idem t)]
  have hinf : infPart D (cA D (Y.e t)) = 0 :=
    GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum (hY.idem t))
  have hm := GlobalTheory.VacMove.isThetaAt_moveLat D ψ A' WW (α t) (α t / β t) (Y.ω' t) hWe Y.rA'.Λ ΛA' Y.rW.Λ ΛW hY.rigA'.1 hA'
    hY.rigW.1 hW g' hg' h hh mA' mW (cA D (Y.e t)) _ Y.vac' (Y.f' t) hee hinf hY.isVac'.2.theta
    (GlobalTheory.ConstRatio.theta_f hY t).2 (hY.snd t)
  rw [hv' t] at hm
  have hm2 := isThetaAt_rescale (hr t).2 hm
  have hΦ : (fun x => stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β (actO A' WW g'⁻¹ h⁻¹ x)) =
      stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW (Lev.finE A' g' * Y.rA'.β) (Lev.finE WW h * Y.rW.β) :=
    funext fun x => (stdSnd_move _ _ _ _ _ _ _ _ _ _ x).symm
  rw [hΦ] at hm2
  exact hm2

end GlobalTheory.BotMoveSnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepFactorInverseAwayUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqTwist

theorem twist_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hvT hvS s z hf
  classical
  set τ := Bs.τ v with hτ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hunder : w.under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under τ
  have hloc : w ∈ locPl G t := hB.2.2.2 v hvT
  have hW0 : w ∉ G.pl.W0 := by
    intro h
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h
    apply hvS
    have := G.pl.under_w hu
    rw [hu'] at this
    rw [← hunder, this]
    exact hu
  have htw : w ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  have hQ : w ∈ Lc.Q t := by
    rcases Finset.mem_union.1 hloc with h | h
    · exact absurd h hW0
    · exact h
  have hq : Ideal.absNorm w.asIdeal = Ideal.absNorm v.1.asIdeal := GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ
  have hQn : 0 < Qn G t := by
    unfold Qn
    refine Finset.prod_pos fun u _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hqd : Ideal.absNorm v.1.asIdeal ∣ Qn G t := hq ▸ Finset.dvd_prod_of_mem _ htw
  obtain ⟨hmu, hchi⟩ := GlobalTheory.T.mu0_and_chiH_unrAt_outside_S0 G hL i j t w hQ (by rw [hunder]; exact hvS)
  have hc := GlobalTheory.T.twistPlace_stepCharacter_conductorExponent_one G hL i j t τ hmu hchi hQ
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.gaussSum_stepCharacter_twistPlace_dvd G W S hL hN i j t τ Bs.ψ (hB.2.2.1 v.1 v.2) hloc hc
  obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist G W S hL hN i j t τ hmu hchi htw
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  set s' : (Fv D.host.F v.1)ˣ := Units.map (Int.castRingHom _).toMonoidHom s with hs'

  have hs2 : s' ^ 2 = 1 := by
    rw [hs', ← map_pow, Int.units_sq, map_one]
  have hsgn : ((ν s' : ℂˣ) : ℂ) = 1 ∨ ((ν s' : ℂˣ) : ℂ) = -1 := by
    have h2 : ((ν s' : ℂˣ) : ℂ) * ((ν s' : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← sq, hs2, map_one, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  obtain ⟨e, he, hea⟩ : ∃ e : D.what₂.LL, D.what₂.embLL e = ((ν s' : ℂˣ) : ℂ) ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) e := by
    rcases hsgn with h | h
    · exact ⟨1, by rw [map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ one_pos (one_pow 1)⟩
    · exact ⟨-1, by rw [map_neg, map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ two_pos (by norm_num)⟩

  set q : ℕ := Ideal.absNorm v.1.asIdeal with hqdef
  have hqa : GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ (-z)) := by
    have hn : ∀ n : ℕ, GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ n) := by
      intro n
      have h1 : (((q : 𝓞 D.what₂.LL) ^ n : 𝓞 D.what₂.LL) : D.what₂.LL) = (q : D.what₂.LL) ^ n := by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
      rw [← h1]
      apply GlobalTheory.Square.AwayClosure.of_dvd (k := n)
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hqd) n
    rcases Int.eq_nat_or_neg (-z) with ⟨n, hn' | hn'⟩
    · rw [hn', zpow_natCast]; exact hn n
    · rw [hn', zpow_neg, zpow_natCast]; exact GlobalTheory.Square.AwayClosure.inv hQn (hn n)
  have hga : GlobalTheory.Square.IsAwayUnit (Qn G t) (g : D.what₂.LL) :=
    GlobalTheory.Square.AwayClosure.of_dvd (k := 1) (by rw [pow_one]; exact hgd.trans (Nat.cast_dvd_cast hqd))
  set a : D.what₂.LL := e * ((q : D.what₂.LL) ^ (-z) * (g : D.what₂.LL) * x) with ha
  have haA : GlobalTheory.Square.IsAwayUnit (Qn G t) a :=
    GlobalTheory.Square.AwayClosure.mul hea (GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul hqa hga) hxa)
  have hfa : D.what₂.embLL a = ((ν s' : ℂˣ) : ℂ) * eps Bs.ψ ν z := by
    rw [ha]
    unfold eps
    rw [hc]
    simp only [map_mul, map_zpow₀, map_natCast, he, hg, hx, Nat.cast_one, pow_one]
    congr 1
    rw [neg_one_mul]
  refine ⟨a⁻¹, GlobalTheory.Square.AwayClosure.inv hQn haA, ?_⟩
  rw [map_inv₀, ← hfa]
  rw [← hfa] at hf
  exact inv_mul_cancel₀ hf

end GlobalTheory.SqTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFields
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistedRatBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem exists_base_lift (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) (i : Fin D.R.m) :
    ∃ (x₀ : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x₀) ∧ (R.FW i).j (sg0 D A) y ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hd : 0 < Module.finrank D.what₂.LL (R.WL F false i) := hRk.1.trans_eq (hRk.2 i).symm
  obtain ⟨y, hy⟩ : ∃ y, (GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y = fun _ => 1 :=
    ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1
      hB.2.1 i A.μ0).2 _
  have h1 := GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 y
  refine hn ⟨(A.fam.L i A.μ0).toF (GlobalTheory.OntoChain.liftLvl F) (GlobalTheory.OntoChain.liftSub R F i A.μ0) y,
    GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y), h1, fun h0 => ?_⟩
  have h2 : GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y) = 0 :=
    (injective_iff_map_eq_zero _).1 (j_injective hU i) _ h0
  have h3 := (injective_iff_map_eq_zero _).1 (GlobalTheory.OntoChain.coordMap_injective (R := R) (F := F) i) _ h2
  exact one_ne_zero (congrFun (hy.symm.trans h3) ⟨0, hd⟩)

theorem baseLiftNeZero (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) :
    ∀ i, ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0 := fun i =>
  (exists_base_lift hU hB hRk i).imp fun _ h => h.elim fun _ h => h.1.symm.trans_ne h.2

theorem twistedRational_of_rayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hC hio hU hO hQ hrow hB hRk hray
  exact GlobalTheory.TwistedClassSum.twistedRational hC fw hio hU hO hQ hrow
    (GlobalTheory.TwistField.coverField_of_containsRayField D G Pl0 T0 A J R fw.laws hC.lev hQ hray) (baseLiftNeZero hU hB hRk)

end GlobalTheory.TwistedRatBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndexStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveMatch_of_markRel_of_isLevMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → l.A = 1 → Pinned U e F ik φ → ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ) (γ : Dw.La →ₗ[𝓞 E] Dw.La) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ → IsLevMove ρ ν γ LinearMap.id → MoveMatch U U k k' h ρ ν := by
  first | exact @GlobalTheory.GeoLevel.moveMatch_of_markRel | exact GlobalTheory.GeoLevel.moveMatch_of_markRel | (intros; apply GlobalTheory.GeoLevel.moveMatch_of_markRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricActionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  first | exact @GlobalTheory.HolDict.lUnif_topR_of_geoAct | exact GlobalTheory.HolDict.lUnif_topR_of_geoAct | (intros; apply GlobalTheory.HolDict.lUnif_topR_of_geoAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalfStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  first | exact @GlobalTheory.UnipModHalf.unip_mod_half | exact GlobalTheory.UnipModHalf.unip_mod_half | (intros; apply GlobalTheory.UnipModHalf.unip_mod_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdealStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  first | exact @GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | exact GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | (intros; apply GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul <;> assumption)
end

