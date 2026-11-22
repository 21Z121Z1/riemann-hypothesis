import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0784
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0785
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0845
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllTriplesLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem exists_sig_of_row (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hOcc : EigOcc D S θ hL Sb eig) (hall : D.nexp.sig_all) (i : D.ntw.Tw) (b : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (hiso : D.what₂.isot j σ ≠ ⊥) (hgood : D.nd.goodRow σ) :
    ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P →
      P ∉ D.ntw.S0 i → eig j (Bs.rowS i s) k P = eig j σ k P := by
  classical
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc j h1 h2 σ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i b x hx0
  set e := Bs.eF i j b h1 h2 with he
  have hfix : MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))
      (G0g D.nd) (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b)
      (e.symm (Φ x)) = e.symm (Φ x) := by
    letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A j).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  have hhk : ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      D.nexp.hkF i j b k P (e.symm (Φ x)) =
        (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
          (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P))) • e.symm (Φ x) := by
    intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply]
    have h3 := hΦT (hL j k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm
  obtain ⟨s, hj, hb, hs⟩ := hall i j b (e.symm (Φ x))
    (fun k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
      (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P)))
    (by simpa using hΦ0) hfix hhk
  refine ⟨s, hj, hb, fun k P hk1 hk2 hsp hP => ?_⟩
  have h3 := hs k P hk1 hk2 hsp hP
  rw [Bs.rowS_eig i s k P hk1 hk2 hsp hP] at h3
  subst hj hb
  have hu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i (D.ntw.side i s) P : D.ntw.O i) ^ k ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact (Bs.cHk i (D.ntw.side i s) P).ne_zero
  exact (readLL0 S i (D.ntw.side i s)).injective (mul_left_cancel₀ (M₀ := FractionRing (D.ntw.O i)) hu h3)

end GlobalTheory.RowTriple

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem tripAll_of_sideB (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hT : EigTrue D cf Rw Sb eig) (hOcc : EigOcc D S θ hL Sb eig) (hP : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw)
    (hall : D.nexp.sig_all) (hloc : ∀ a σ v, IsSplitPl D.host v → D.naut.locW a σ v = Rw.locR σ v)
    (hR : ∀ a, ReadTw D a) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.TripAll D := by
  classical
  intro a σ hσ
  obtain ⟨hiso, hgood⟩ := hσ
  obtain ⟨h1, h2⟩ := D.nd.j_range a
  obtain ⟨s, hj, hb, he⟩ := exists_sig_of_row D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc hall (D.ntw.twOf a)
    (D.ntw.twSide a) (D.nd.j a) h1 h2 σ hiso hgood
  obtain ⟨hiso', hgood', -⟩ := Bs.rhoS _ s
  rw [hj] at hiso'
  refine ⟨s, hj, hb, GlobalTheory.T.isRhoOfRow_of_frobenius_eigenvalues D Rw Bs.rowS Bs.rhoS hP a σ s (hR a) hb hj ⟨hiso, hgood⟩ (hloc a σ) ?_⟩
  have hfin : ((Sb ∪ D.ntw.S0 (D.ntw.twOf a) : Finset (PlE D.host)) : Set (PlE D.host)).Finite := Finset.finite_toSet _
  filter_upwards [hfin.compl_mem_cofinite] with P hP' hsp
  have hP1 : P ∉ Sb := fun h => hP' (by simp [h])
  have hP2 : P ∉ D.ntw.S0 (D.ntw.twOf a) := fun h => hP' (by simp [h])
  exact GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius D cf Rw Sb eig hT hP (D.nd.j a) h1 h2 σ (Bs.rowS _ s) hiso hgood hiso' hgood' P hsp hP1
    fun k hk1 hk2 => he k P hk1 hk2 hsp hP2

theorem allTriples_atMem : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  intro hP hS hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.T.galois_family_place_data hP hS hL) fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨cf, Rw, low, Pq, S, hL', eig, θ, Bs, Sb, hSb, hKs, hT, hOcc, hcp, hall, hloc, hR⟩ := h
  exact GlobalTheory.TwistedSelmerCompare.allTriples_of_tripAll _
    (tripAll_of_sideB _ cf Rw low Pq S hL' eig θ Bs Sb hSb hKs hT hOcc hcp hall hloc hR)

end GlobalTheory.RowTriple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.published_inputs_imply_conclusion : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N Ng : NExt hL), StepW Start (Has3 (prmR N SExt.none (geoCl anyGeometry)).s) → LevelThreeCondition (prmR N SExt.none (geoCl anyGeometry)).s → LevelThreeCondition (prmR Ng SExt.none (geoCl anyGeometry)).s → ExportF KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) → Pass KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR Ng SExt.none (geoCl anyGeometry)).s K B f T w) → (∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd) → MemberE (prmR N SExt.none (geoCl anyGeometry)).s := by
  first | exact @GlobalTheory.Mem.Top.Closing.memberE_closing | exact GlobalTheory.Mem.Top.Closing.memberE_closing | (intros; apply GlobalTheory.Mem.Top.Closing.memberE_closing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
end
end

