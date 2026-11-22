import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftVectorEqUnitMulDilatedFlatDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsFockFormEqOfMemMtLat
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0999
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoefficientsIntegralCoreForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftVectorEqUnitMulDilatedFlatDatumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_vector_eq_unit_mul_dilated_flat_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ Gc : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) Gc ∧ IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → R.vP i t = Tm (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) := by
  first | exact @GlobalTheory.LiftFlatModel.lift_eq_model_flat | exact GlobalTheory.LiftFlatModel.lift_eq_model_flat | (intros; apply GlobalTheory.LiftFlatModel.lift_eq_model_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeFockPolysSpanIntegralForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
  (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) =
    Submodule.span (intLL D) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1)) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  classical
  have key := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  have hrat := UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  obtain ⟨e, -, htie, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · intro F hF
    obtain ⟨m, rfl⟩ := hrat F hF
    obtain ⟨a, ha⟩ := (key m).1 hF
    rw [ha, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [map_smul, smul_comm]
    refine Submodule.smul_mem _ (⟨D.what₂.embLL (a v : D.what₂.LL), a v, rfl⟩ : intLL D) (Submodule.subset_span ?_)
    obtain ⟨x, hx⟩ := htie.1 v hv
    have hx' : D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) = v := hx
    exact ⟨e x, by show D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen; rw [hx']; exact hv, by simp only [hx']⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine (key m).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m)]
    · simp
    · intro v _ hv
      simp [hv]
    · exact fun h => absurd hm h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIsotypicInnerNeZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.LiftSplitLoc

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in

theorem locG_rankOne {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = rcAt hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl

set_option maxHeartbeats 1000000 in

theorem read (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    (hH : GlobalTheory.Published.HoweDualityGL) (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} {cf : CharFrame D}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {Rw : RowSide D} (a : ParIn hL D cf rep Rw) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (P : NG.AutRep D.host.E D.R.nV) (μ : D.naut.CG 1)
    (hμ : (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩) (s : SplitPlace D.host.E)
    (π : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hπ : IsLocS (n := D.R.nV) P.S s π)
    (hτ : IsLocS (rep σ).S s τ) (hU : IsUnitarisable τ.ρ)
    (hP : ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ
      (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w)))) :
    D.nbc.locAU j (a.A.cls j h1 h2 P) s.w =
      D.naut.lpChar (D.naut.lpSum (Rw.locR σ s.w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ s.w))
        (D.naut.locG D.naut.etaTinv s.w) := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have L : RecLaws (rcAt hL D s.w) := (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s.w)).recLaws
  set χ := cf.mu0 ⟨j - 1, by omega⟩ with hχ
  have hμc : IsComp χ s.w (χ.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ s.w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, hunit⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ s.w
  have hχu : χ.IsUnitary := hμ ▸ (a.chr.e1 μ).2
  have hμU : IsUnitaryChar (χ.loc s.w) := fun x => by
    rw [huniq _ hμc]; exact hunit hχu x
  have hηc : IsComp cf.eta s.w (cf.eta.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc cf.eta s.w, fun _ => rfl⟩
  have hηi : IsComp (a.chr.e1 D.naut.etaTinv).1 s.w ((cf.eta⁻¹).loc s.w) := by
    rw [a.chr.etaTinv]
    exact ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc _ s.w, fun _ => rfl⟩
  have hinv : (cf.eta⁻¹).loc s.w = (cf.eta.loc s.w)⁻¹ := MonoidHom.ext (HChar.loc_inv _ _)
  have hrt : D.R.r < D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  let π₀ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t) := Irr.ofIrrRep π
  let π' := GlobalTheory.SplitPairLift.twistIrr π₀ hηc.1
  let τ₀ : Irr (s.w.adicCompletion D.host.E) D.R.r := Irr.ofIrrRep τ
  let cμ := GlobalTheory.SplitPairLift.detIrr 1 hμc.1
  let τμ := GlobalTheory.SplitPairLift.detIrr D.R.t hμc.1
  let cη := Irr.ofDet 1 ((cf.eta⁻¹).loc s.w) hηi.1
  have e1 : Nonempty (π'.π.Equiv (prod₂ τ₀.π τμ.π)) :=
    GlobalTheory.T.theta_correspondence_large_rank hBZ hB hH _ D.R.r D.R.t _ _ _ τ.ρ π'.π hrt hμc.1 hμU τ.smooth τ.irr hU π'.smooth π'.irr hP
  have e2 := L.prod _ _ τ₀ τμ π' e1
  have e3 := L.det D.R.t _ cμ τμ ⟨.refl _⟩ ⟨.refl _⟩
  have e4 := L.twist _ (cf.eta.loc s.w)⁻¹ cη π' π₀ (by rw [← hinv]; exact ⟨.refl _⟩) (by
    show Nonempty (π₀.π.Equiv (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π₀.π (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w))) (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w)⁻¹)))
    rw [GlobalTheory.SplitPairLift.twist_twist_inv]
    exact ⟨.refl _⟩)
  have eμ := locG_rankOne a.T a.cg a.chr μ s.w (χ.loc s.w) (hμ ▸ hμc)
  have eη := locG_rankOne a.T a.cg a.chr D.naut.etaTinv s.w _ hηi
  have hau : a.T.e s.w (D.nbc.locAU j (a.A.cls j h1 h2 P) s.w) = rcAt hL D s.w _ π₀ := a.au j h1 h2 P s π hπ
  have hrow : a.T.e s.w (Rw.locR σ s.w) = rcAt hL D s.w _ τ₀ := a.row.1 σ s τ hτ
  have h7 : D.naut.lpDim (D.naut.locG D.naut.etaTinv s.w) = 1 := by
    rw [← a.T.dim, eη, L.dim]
  apply (a.T.e s.w).injective
  rw [a.T.char _ _ _ h7, a.T.sum, GlobalTheory.SplitPairLift.e_spehLoc, hau, hrow, e4, e2, e3, eη, eμ]
  rfl

end GlobalTheory.LiftSplitLoc

namespace GlobalTheory.LiftSplitLoc

set_option maxHeartbeats 1000000 in

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hP hL
  have hA := GlobalTheory.T.split_pair_theta_lowest hP hL
  have hB := GlobalTheory.T.local_components_unitarisable hP hL
  unfold GlobalTheory.LiftRef.AtRows at hA hB ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hB fun K B f T w Z Wt hX z p0 Y HA HB Rw a M tup Q hM hI j h1 h2 σ S hS hpair μ hμ v hv => ?_
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w _ v hv
  have hne : (w.st Z).toD7.what₂.isot j σ ≠ ⊥ := by
    obtain ⟨y, hy, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hy
    apply hF
    rw [hy, map_zero, inner_zero_right]
  obtain ⟨τ, hτ, hU⟩ := HB Rw a M tup Q hM hI j σ hne s
  obtain ⟨π, hπ⟩ := GlobalTheory.LocCompSplit.exists_isLocS (GlobalTheory.LiftRef.autOf (M _ j h1 h2) S hS) s
  exact read hP.what₂.bz hP.what₂.bern hP.what₂.howe hL a j h1 h2 σ _ μ hμ s π τ hπ hτ hU
    (HA Rw a M tup Q hM hI j h1 h2 σ S hS hpair s π τ hπ hτ)

end GlobalTheory.LiftSplitLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRationalStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_base_twisted_universal_rational : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK → RatHyp T Rl F κ v₀ O i j hV → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.SeriesTie.RatAll.ratRow | exact GlobalTheory.SeriesTie.RatAll.ratRow | (intros; apply GlobalTheory.SeriesTie.RatAll.ratRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoefficientsIntegralCoreFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_series_coefficients_integral_core_forms : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∀ hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j, ∃ la : HeightOneSpectrum (𝓞 X.core.Q.c.F), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) ∧ ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) := by
  first | exact @GlobalTheory.XiIntSteps.xi_int_core_forms | exact GlobalTheory.XiIntSteps.xi_int_core_forms | (intros; apply GlobalTheory.XiIntSteps.xi_int_core_forms <;> assumption)
end

