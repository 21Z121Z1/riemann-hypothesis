import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0776
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0954
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
import Formalism.LocalToGlobal.Columns.MtAdWt
import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0788
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0777
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0778
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopiStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ → ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q → ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  first | exact @GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | exact GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | (intros; apply GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopiesStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanInputsImplyStatement
section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_inputs_imply : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.BesselUniquenessReal → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → HypA := by
  first | exact @GlobalTheory.hypA_of_artinReciprocity | exact GlobalTheory.hypA_of_artinReciprocity | (intros; apply GlobalTheory.hypA_of_artinReciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_form_base_change_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : R →+* W), Function.Injective g → ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  first | exact @GlobalTheory.TraitCmp.main | exact GlobalTheory.TraitCmp.main | (intros; apply GlobalTheory.TraitCmp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.LevCmp
open Formalism.L2.DIV GlobalTheory.CoefModel

section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem match_mtwRat (γ : GQ L n) : (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
    ((Formalism.L2.Col.mtwRat γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom :=
  (congrArg Units.val (Formalism.L2.Col.mtwInc_mtwRatFun γ)).symm

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; subst h; rfl

end Gen2

set_option maxHeartbeats 4000000 in

theorem cellWt_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  intro hN hL
  refine StepW.of_all fun K B f T w _ _ _ P x l v i b ψ hA j hTw hl hok e hSR => ?_
  have hemb : ∀ t, Formalism.L2.embT (Dof x) t = Formalism.BasicNotions.TH.tauE (Dof x) t := fun t => rfl
  have hinj : Function.Injective (Formalism.L2.embT (Dof x)) := GlobalTheory.StdRat.tauE_injective (Dof x)
  have hcm : ∀ t t', Formalism.L2.embT (Dof x) t ≠ ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t') := by
    intro t t' h
    have h1 := (GlobalTheory.StdRat.tauE_cm (Dof x) (Formalism.L2.embT (Dof x) t')).1 ⟨t', rfl⟩
    exact h1 ⟨t, h⟩
  have hcov : ∀ σ : (Dof x).host.E →+* ℂ, ∃ t, σ = Formalism.L2.embT (Dof x) t ∨
      σ = ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) := by
    intro σ
    by_cases h : ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨t, Or.inl ht.symm⟩
    · have h2 : ¬ ¬ ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = ComplexEmbedding.conjugate σ :=
        fun h' => h ((GlobalTheory.StdRat.tauE_cm (Dof x) σ).2 h')
      obtain ⟨t, ht⟩ := not_not.1 h2
      refine ⟨t, Or.inr ?_⟩
      rw [hemb, ht]
      simp
  have hcj : ∀ y, NX.cE (Dof x) y = IsCMField.complexConj (Dof x).host.E y := by
    intro y
    show (Dof x).host.conj y = _
    symm
    apply (Dof x).host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hke : ∀ t, (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t) = Formalism.L2.embT (Dof x) t := by
    intro t
    ext y
    have h1 := hSR (NX.embEL0 (Dof x) (((Dof x).host.sigmaOf ((Dof x).eTau t : (Dof x).R.GG)) y))
    refine Eq.trans ?_ (h1.trans (NX.embLL_embEL0 (Dof x) t y))
    rfl

  obtain ⟨lamC, T', hT'⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau (Formalism.L2.embT (Dof x)) hinj hcm hcov
    (mtAt l.mt.M v j).wt
  have hT'r : ∀ γ y, T' ((mtAt l.mt.M v j).wt.ρ γ y) =
      rhoVr (Formalism.L2.embT (Dof x)) lamC (Formalism.L2.Col.mtwRat γ) (T' y) :=
    fun γ y => hT' γ _ (match_mtwRat γ) y
  have hinj' : Function.Injective (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x))) := by
    intro t t' h
    apply hinj
    have := congrArg ComplexEmbedding.conjugate h
    simpa [Formalism.L2.Col.mtwConj] using this
  have hcm' : ∀ t t', Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t ≠
      ComplexEmbedding.conjugate (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t') := by
    intro t t' h
    have h2 : ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) = Formalism.L2.embT (Dof x) t' := by
      simpa [Formalism.L2.Col.mtwConj] using h
    exact hcm t' t (by rw [← h2])
  have hten := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line
    (Formalism.L2.embT (Dof x)) hinj hcm lamC
  have hten' := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line _ hinj' hcm' lamC
  have hiso : (Formalism.L2.Col.mtWt (Formalism.L2.embT (Dof x)) lamC hten).Iso (mtAt l.mt.M v j).wt :=
    ⟨T'.symm, fun γ y => by
      apply T'.injective
      have hs : ∀ z, T' (T'.symm z) = z := fun z => T'.apply_symm_apply z
      erw [hT'r, hs, hs]
      rfl⟩
  have hdual := GlobalTheory.WtDual.isDual_of_iso hiso (Formalism.L2.Col.mtWt_isDual _ lamC hten hten')
  have hC : ∀ t, NG.infOf (lamC t).w = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := fun t =>
    l.mt.mt.wt _ j t _ _ hdual (Formalism.L2.Col.tenWt_hwAt _ hinj hcm lamC hten' t)

  have hj1 : 1 ≤ j.1 + 1 := by omega
  have hj2 : j.1 + 1 ≤ (Dof x).R.m := by omega
  choose lam0 hlam0 using fun t => l.b.Bs.exp.rhoW_hw i (j.1 + 1) b t hj1 hj2
  obtain ⟨lamK, hlamK, TK, hTK⟩ := GlobalTheory.T.irreducible_weight_descends_to_polynomial_module (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau
    (FractionRing ((Dof x).ntw.O i)) (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b)
    (by intro t t' h; beta_reduce at h; rw [hke, hke] at h; exact hinj h)
    (by intro t t'; beta_reduce; rw [hke, hke]; exact hcm t t')
    (by intro σ; beta_reduce; simp only [hke]; exact hcov σ)
    (NX.cE (Dof x)) hcj _ (l.b.Bs.exp.rhoW i (j.1 + 1) b) (l.b.Bs.exp.rhoW_irr i (j.1 + 1) b hj1 hj2) lam0 hlam0
  have hK : ∀ t, NG.infOf (lam0 t) = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := by
    intro t
    rw [l.b.Bs.exp.rhoW_wt i (j.1 + 1) b t hj1 hj2 _ (lam0 t) (GlobalTheory.FitHecke.infG_etaT l.a.A.chr t) (hlam0 t)]
    congr 1
    push_cast
    ring
  have hlam : lamK = lamC := by
    funext t
    apply domWeight_ext
    apply GlobalTheory.MtRead.eq_of_infOf_eq (lamK t).anti (lamC t).anti
    rw [hlamK t, hK t, hC t]
  subst hlam
  have hTK' : ∀ γ y, TK (l.b.Bs.exp.rhoW i (j.1 + 1) b γ y) =
      rhoVr (NX.kEmb (Dof x) i b) lamK (Formalism.L2.Col.mtwRat γ) (TK y) := fun γ y => hTK γ _ (match_mtwRat γ) y
  have hfun : (fun t => (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t)) = Formalism.L2.embT (Dof x) :=
    funext hke
  have h1 := GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b) lamK _ (mtAt l.mt.M v j).wt.ρ TK hTK'
    T' (by rw [hfun]; exact hT'r)
  unfold CellWt
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).acg
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).mod
  exact GlobalTheory.T.matchingMatrices_of_baseChange_representation (NX.toKk (Dof x) i (T.k v)) e (l.b.Bs.exp.rhoW i (j.1 + 1) b) (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).ρ
    (mtAt l.mt.M v j).wt.ρ (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).bc h1

end GlobalTheory.LevCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAtStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_nontrivial_at : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  first | exact @GlobalTheory.FrameTypes.main | exact GlobalTheory.FrameTypes.main | (intros; apply GlobalTheory.FrameTypes.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainInvariant
section
open Formalism.DegreeFormula

open Matrix Formalism.MJ Formalism.UG GlobalTheory.HodgeDomain GlobalTheory.HermFrame GlobalTheory.TrueCx
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem unflat_zero : unflat (0 : ι × Fin p × Fin q → ℂ) = 0 := by
  funext i; ext a b; rfl

theorem exists_upqI {z : ι → Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ DomI ι p q) :
    ∃ g ∈ UpqI ι p q, moebI g 0 = z := by
  have : ∀ τ, ∃ g : GL (Fin p ⊕ Fin q) ℂ, g ∈ Upq p q ∧ moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := by
    intro τ
    obtain ⟨g, hg, hgz⟩ := GlobalTheory.TrueCx.FrameOnto.exists_moeb_zero (hz τ)
    have hd : g.det ≠ 0 := by
      intro h0
      have h1 := congrArg det hg
      have h2 := congrArg det (Jpq_sq (p := p) (q := q))
      rw [det_mul, h0, mul_zero] at h1
      rw [det_mul, ← h1] at h2
      simp at h2
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 hg, hgz⟩
  choose g hg hgz using this
  exact ⟨g, fun τ _ => hg τ, funext fun τ => hgz τ⟩

theorem normSq_det_jW {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq (jW g 0).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hP_moeb hg (zero_mem_hcDom p q)
  have e0 : hP (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hP]
  rw [e0, Matrix.mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_conjTranspose, hP, det_one_sub_mul_comm] at h2
  rw [hQ, ← h2, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem normSq_det_kapQ_inv {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq ((kapQ g 0)⁻¹).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hQ_moeb hg (zero_mem_hcDom p q)
  have e0 : hQ (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hQ]
  rw [e0] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_conjTranspose, det_one] at h2
  set d := (kapQ g 0).det
  set H := (hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det
  have h3 : H * ((Complex.normSq d : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, ← h2, Complex.star_def]; ring
  have h4 : H = ((Complex.normSq d : ℝ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, h4, ← Complex.ofReal_inv, Complex.ofReal_re]

end GlobalTheory.DomDensInv

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem det_flat_mul (A : ι → Matrix (Fin p) (Fin p) ℂ) (B : ι → Matrix (Fin q) (Fin q) ℂ)
    (L : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
    (hL : ∀ x, L x = flat (fun τ => A τ * unflat x τ * B τ)) :
    LinearMap.det L = ∏ τ, (A τ).det ^ q * (B τ).det ^ p := by
  let E : (ι × Fin p × Fin q → ℂ) ≃ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ) :=
    { toFun := unflat, invFun := flat, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have key : (E : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ)) ∘ₗ L ∘ₗ
      (E.symm : (ι → Matrix (Fin p) (Fin q) ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      LinearMap.pi fun τ => (GlobalTheory.ModuLR.lrLin (A τ) (B τ)).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => funext fun τ => ?_
    change unflat (L (flat x)) τ = A τ * x τ * B τ
    rw [hL]; rfl
  rw [← LinearMap.det_conj L E, key, LinearMap.det_pi]
  simp only [GlobalTheory.ModuLR.det_lrLin, Fintype.card_fin]

theorem model_smooth (h : Fintype.card (ι × Fin p × Fin q) = n) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : GlobalTheory.UnifDens.flatL h u ∈ DomFlat ι p q) (τ : ι) :
    MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) u ∧
      IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)ᵀ).det := by
  have hp := hP_posDef (hu τ)
  have hunit : IsUnit (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ)).det := hp.det_pos.ne'.isUnit
  refine ⟨MContDiffAt.transpose (MContDiffAt.inv ?_ hunit), ?_⟩
  · have hY : MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ) u := by
      intro a b
      have e : (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ a b) =
          fun w => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι × Fin p × Fin q => ℂ) (τ, a, b)).comp
            (GlobalTheory.UnifDens.flatL h : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ))).restrictScalars ℝ) w := rfl
      rw [e]; exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact (mContDiffAt_const 1).sub (hY.mul hY.conjTranspose)
  · rw [det_transpose]; exact isUnit_nonsing_inv_det _ hunit

theorem gram_transpose_of_congr {J Hg Hy : Matrix (Fin p) (Fin p) ℂ} (hJ : IsUnit J.det) (h : Jᴴ * Hg * J = Hy) :
    Hgᵀ = (J⁻¹)ᵀ * Hyᵀ * ((J⁻¹)ᵀ)ᴴ := by
  have hJ' : IsUnit Jᴴ.det := by rw [det_conjTranspose]; exact hJ.star
  have h1 : Hg = (J⁻¹)ᴴ * Hy * J⁻¹ := by
    rw [← h, conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hJ', Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.mul_one]
  rw [h1, transpose_mul, transpose_mul]
  have e : ((J⁻¹)ᴴ)ᵀ = ((J⁻¹)ᵀ)ᴴ := by ext i j; rfl
  rw [e, Matrix.mul_assoc]

theorem chernTop_model_moeb : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  intro ι _ p q n h v hv
  classical
  set e := GlobalTheory.UnifDens.flatL h with he
  set K : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ := fun u τ => ((hP (unflat (e u) τ))⁻¹)ᵀ with hK
  set R : MvPolynomial (ι × ℕ) ℝ := ∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q with hR
  set z := unflat (e v) with hz
  have hzD : z ∈ DomI ι p q := hv
  obtain ⟨g, hg, hgz⟩ := exists_upqI hzD
  set Φ : (ι × Fin p × Fin q → ℂ) → (ι × Fin p × Fin q → ℂ) := fun w => flat (moebI g (unflat w)) with hΦ
  set φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n := fun u => e.symm (Φ (e u)) with hφ
  have h0D : (0 : ι × Fin p × Fin q → ℂ) ∈ DomFlat ι p q := by
    intro τ; rw [unflat_zero]; exact zero_mem_hcDom p q
  have he0 : e 0 = 0 := map_zero e
  have hφ0 : φ 0 = v := by
    show e.symm (flat (moebI g (unflat (e 0)))) = v
    rw [he0, unflat_zero, hgz]
    exact e.symm_apply_apply v
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hΦan : AnalyticAt ℂ Φ 0 := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd 0 h0D
  have hΦan' : AnalyticAt ℂ Φ (e 0) := by rw [he0]; exact hΦan
  have hφan : AnalyticAt ℂ φ 0 :=
    (e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).analyticAt _ |>.comp
      (hΦan'.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).analyticAt 0))
  have hKv := fun τ => model_smooth h (u := v) hv τ
  have h0S : e 0 ∈ DomFlat ι p q := by rw [he0]; exact h0D
  have hK0 := fun τ => model_smooth h (u := 0) h0S τ

  have hA := GlobalTheory.ChernPull.chernTop_comp R K φ 0 hφan (by rw [hφ0]; exact fun τ => (hKv τ).1)
    (by rw [hφ0]; exact fun τ => (hKv τ).2)
  rw [hφ0] at hA

  set S : Set (ReciprocityTheory.L2DbarEstimates.V n) := e ⁻¹' DomFlat ι p q with hS
  have hSo : IsOpen S := ho.preimage e.continuous
  have h0S' : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ S := h0S
  set g' : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ :=
    fun w τ => ((jW (g τ) (unflat (e w) τ))⁻¹)ᵀ with hg'
  have hΦcd : ContDiffOn ℂ 1 Φ (DomFlat ι p q) :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd).contDiffOn ho.uniqueDiffOn
  have hΨ : ContDiffOn ℂ 1 (fun w => Φ (e w)) S :=
    hΦcd.comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).contDiff.contDiffOn fun w hw => hw
  have hg'an : ∀ τ i j, AnalyticAt ℂ (fun w => g' w τ i j) 0 := by
    intro τ i j
    have hent : ∀ a b, ContDiffOn ℂ 1 (fun w => jW (g τ) (unflat (e w) τ) a b) S := by
      intro a b
      have ee : (fun w => jW (g τ) (unflat (e w) τ) a b) = fun w =>
          (g τ).1.toBlocks₁₁ a b - ∑ k, Φ (e w) (τ, a, k) * (g τ).1.toBlocks₂₁ k b := by
        funext w; simp only [jW, Matrix.sub_apply, Matrix.mul_apply]; rfl
      rw [ee]
      exact contDiffOn_const.sub (ContDiffOn.sum fun k _ => ((contDiffOn_pi.1 hΨ) (τ, a, k)).mul contDiffOn_const)
    have hinv := GlobalTheory.HodgeDomain.ActionDeriv.diffOn_inv (s := S) (M := fun w => jW (g τ) (unflat (e w) τ)) hent
      (fun w hw => (jW_isUnit (hg τ (Set.mem_univ _)) (hw τ)).ne_zero) j i
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hSo (hinv.differentiableOn one_ne_zero) 0 h0S'
  have hg'u : ∀ τ, IsUnit (g' 0 τ).det := by
    intro τ
    rw [hg', det_transpose]
    exact isUnit_nonsing_inv_det _ (jW_isUnit (hg τ (Set.mem_univ _)) (h0S τ))
  have hev : ∀ᶠ w in nhds (0 : ReciprocityTheory.L2DbarEstimates.V n), ∀ τ, K (φ w) τ =
      (((fun _ : ι => (1 : ℝ)) τ : ℝ) : ℂ) • (g' w τ * K w τ * (g' w τ)ᴴ) := by
    filter_upwards [hSo.mem_nhds h0S'] with w hw τ
    have hy : unflat (e w) τ ∈ hcDom p q := hw τ
    have hgt := hg τ (Set.mem_univ _)
    have key := gram_transpose_of_congr (jW_isUnit hgt hy) (hP_inv_moeb hgt hy)
    have e1 : K (φ w) τ = ((hP (moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (unflat (e w) τ)))⁻¹)ᵀ := by
      show ((hP (unflat (e (e.symm (Φ (e w)))) τ))⁻¹)ᵀ = _
      rw [e.apply_symm_apply]; rfl
    rw [e1, key, Complex.ofReal_one, one_smul]
  have hB := GlobalTheory.PointChern.chernTop_changeFrame R (fun w => K (φ w)) K g' (fun _ => (1 : ℝ)) 0
    (fun _ => one_pos) hg'an hg'u (fun τ => (hK0 τ).1) (fun τ => (hK0 τ).2) hev

  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ 0) (e 0) := by rw [he0]; exact hΦan.differentiableAt.hasFDerivAt
  have hφd : HasFDerivAt φ ((e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).comp
      ((fderiv ℂ Φ 0).comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)))) 0 :=
    e.symm.hasFDerivAt.comp 0 (hΦd.comp 0 e.hasFDerivAt)
  have hdetF : LinearMap.det (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    refine det_flat_mul _ _ _ fun x => ?_
    have := hD 0 (fun τ => zero_mem_hcDom p q) (unflat x)
    exact this
  have hdet : LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    rw [hφd.fderiv, ← hdetF, ← LinearMap.det_conj (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
      e.symm.toLinearEquiv]
    rfl
  have hx : ∀ τ, Complex.normSq (jW (g τ) 0).det = ((hQ (z τ)).det).re ∧
      Complex.normSq ((kapQ (g τ) 0)⁻¹).det = ((hQ (z τ)).det).re := by
    intro τ
    have hgt := hg τ (Set.mem_univ _)
    have hzτ : moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := congrFun hgz τ
    rw [← hzτ]
    exact ⟨normSq_det_jW hgt, normSq_det_kapQ_inv hgt⟩
  have hN : Complex.normSq (LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) =
      ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := by
    rw [hdet, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_pow, map_pow, (hx τ).1, (hx τ).2, pow_add, mul_comm]
  have hpos : ∀ τ, 0 < ((hQ (z τ)).det).re := fun τ =>
    (Complex.pos_iff.1 (show (hQ (z τ)).PosDef from hzD τ).det_pos).1
  have hNpos : 0 < ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := Finset.prod_pos fun τ _ => pow_pos (hpos τ) _
  rw [hB, hN] at hA
  have e2 : ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ)) = (∏ τ, ((hQ (z τ)).det).re ^ (p + q))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg, zpow_natCast]
  show GlobalTheory.GoodMetric.chernTop R K v = GlobalTheory.GoodMetric.chernTop R K 0 * ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ))
  rw [e2, hA]
  field_simp

end GlobalTheory.DomDensInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOriginStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_boundedDomainModel_eq_mul_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  first | exact @GlobalTheory.PointChern.chernTop_model_eq_mul | exact GlobalTheory.PointChern.chernTop_model_eq_mul | (intros; apply GlobalTheory.PointChern.chernTop_model_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDetStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_comp_holomorphic_normSq_det : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  first | exact @GlobalTheory.ChernPull.chernTop_comp | exact GlobalTheory.ChernPull.chernTop_comp | (intros; apply GlobalTheory.ChernPull.chernTop_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_divisibility_bundle : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), Ind.PIota _ _ c (b.part t) ∧ (Ind.PDiv _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  first | exact @GlobalTheory.ClassSumPinLink.pIota_classSumPin | exact GlobalTheory.ClassSumPinLink.pIota_classSumPin | (intros; apply GlobalTheory.ClassSumPinLink.pIota_classSumPin <;> assumption)
end

