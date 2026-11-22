import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
open GlobalTheory.Grow
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.AdjUnfold

set_option maxHeartbeats 4000000 in

theorem integral_val_thF_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y u
  have hm := hL.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hL.thP.ωP i t
  have hpt := hL.thP.pt_theta i t
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hJt : ∀ k, IsThetaFunO R.ψ (Vc D i) (Wc D i) (jointVec R i t v (b k)) := fun k => hpt _
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ u)
  have hFc : Continuous (R.extV i t u) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t u (γ * h) = R.extV i t u h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hGk : ∀ k, RapidDec (Vc D i) (fun h => ⟪R.extV i t u h, b k⟫_ℂ) := fun k =>
    RapidDec.of_isCompact (fun γ hγ h => by simp only [hFi γ hγ h]) (hFc.inner continuous_const) hK
      (fun g => by
        obtain ⟨γ, hγ, c', hc', e⟩ := hKc g
        exact ⟨γ⁻¹, inv_mem hγ, by rw [e, inv_mul_cancel_left]; exact hc'⟩)
  obtain ⟨-, hr, -⟩ := hm.HW i (sg0 D A)
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  have hF : RapidDec (Wc D i) (fun g => starRingEnd ℂ (val R i v y g)) :=
    (rapidDec_of_cuspForm hP hθ (hTm.aut fun ρ => v ρ) (hTm.cusp fun ρ => v ρ)).conj
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin n → GA D (Wc D i) → GA D (Vc D i) → ℂ, Φ = fun k g h =>
      thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) * starRingEnd ℂ (val R i v y g) *
        starRingEnd ℂ ⟪R.extV i t u h, b k⟫_ℂ := ⟨_, rfl⟩
  have hint : ∀ k, Integrable (Function.uncurry (Φ k))
      (((R.νW i).restrict (R.fdW i)).prod ((R.νV i t).restrict (R.fdV i t))) := fun k => by
    rw [hΦ]
    exact GlobalTheory.ChainOnto.ThetaSwap.integrable_prod hθ hω (hJt k) hHV hfdV hHW hfdW (hGk k) hF
  have hthF : ∀ g, R.thF i t u (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) ∂(R.νV i t) :=
    fun g => (hL.thP.thF i t).elim fun _ h => (congrFun (h.2 u v) g).trans
      (h.1.eq ((R.extV i t).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g)
  have hexp : ∀ g h, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) =
      ∑ k, ⟪b k, R.extV i t u h⟫_ℂ * thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) := by
    intro g h
    have e : (R.cV i).ext ((R.HV i t).e u) h = ∑ k, ⟪b k, R.extV i t u h⟫_ℂ • b k := (b.sum_repr' _).symm
    rw [e, map_sum]
    unfold jointVec RealDat.ptP
    simp only [map_sum, map_smul, thetaKO, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hL1 : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g =
      ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) := by
    have hae : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), ∀ k,
        Integrable (fun h => Φ k g h) ((R.νV i t).restrict (R.fdV i t)) :=
      ae_all_iff.2 fun k => (hint k).prod_right_ae
    filter_upwards [hae] with g hg
    rw [hthF g, ← integral_const_mul]
    have e : ∀ h, star (val R i v y g) * thetaKO (R.ωP i t) h g
        (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) = ∑ k, Φ k g h := by
      intro h
      rw [hexp g h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ, inner_conj_symm, Complex.star_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact integral_finset_sum _ fun k _ => hg k
  have hR : ∀ h, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ = ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) := by
    intro h
    simp only [upVec, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hΦ, upLift]
    rw [integral_mul_const, ← integral_conj, inner_conj_symm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
  calc ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i)
      = ∫ g in R.fdW i, ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) := integral_congr_ae hL1
    _ = ∑ k, ∫ g in R.fdW i, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) :=
        integral_finset_sum _ fun k _ => (hint k).integral_prod_left
    _ = ∑ k, ∫ h in R.fdV i t, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        Finset.sum_congr rfl fun k _ => integral_integral_swap (hint k)
    _ = ∫ h in R.fdV i t, ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        (integral_finset_sum _ fun k _ => (hint k).integral_prod_right).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => (hR h).symm)

end GlobalTheory.AdjUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissibleStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_pair_of_admissible : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D := by
  first | exact @GlobalTheory.PointRepAboveL.main | exact GlobalTheory.PointRepAboveL.main | (intros; apply GlobalTheory.PointRepAboveL.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHeckeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  first | exact @GlobalTheory.SatInd.guMap_comp_mem_hecke | exact GlobalTheory.SatInd.guMap_comp_mem_hecke | (intros; apply GlobalTheory.SatInd.guMap_comp_mem_hecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem conjPl_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem splitSet_of_split {S : Finset (Pl D.host.E)} (hs : ∀ P ∈ S, IsSplitPl D.host P)
    (hn : ∀ P ∈ S, ∀ P' ∈ S, ¬ IsConjPl D.host P P') : SplitSet S := by
  refine GlobalTheory.GridIdem.exists_isIdemSum S (fun P hP => GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne_of_split (hs P hP)))
    fun P hP P' hP' h => ?_
  rcases (GlobalTheory.Mem.TypePl.under_eq_iff P P').1 h.symm with e | e
  · exact e.symm
  · exact absurd e (hn P hP P' hP')

end GlobalTheory.UnivGood

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem univOf_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ),
      (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).Good (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) := by
  intro D N X ρ hρ Y i Q M
  classical
  set A := admissibleConjugatePairPlaces X i Q M with hA
  have hAconj : ∀ P ∈ A, ∀ P', IsConjPl D.host P P' → P' ∈ A := fun P hP P' hc => conj_mem_admissibleConjugatePairPlaces hP hc
  have hsplit : SplitSet (half (ρ.ch i) A) := by
    refine splitSet_of_split (fun P hP => isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) hc
    exact ((hρ.ch i).pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  refine ⟨hsplit, fun PP hPP => ?_⟩
  have hPA : PP ∈ A := (mem_half.1 hPP).1
  obtain ⟨-, P', hP'Q, hc, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPA
  have hP'A : P' ∈ A := conj_mem_admissibleConjugatePairPlaces hPA hc
  set φ := coord Y i A M PP with hφ
  have hco : ∀ σ, Multiplicative.toAdd (φ σ) = Multiplicative.toAdd (Y.delU i A M σ) ⟨PP, hPA⟩ :=
    fun σ => coord_apply Y i A M hPA σ
  have hord : ∀ σ, ∃ n : ℕ, φ σ ^ (X.l i ^ n) = 1 := fun σ => ⟨M, by
    rw [← ofAdd_toAdd (φ σ), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩
  have hopen : IsOpen (φ.ker : Set (G D.host.E N.Om)) := by
    refine Subgroup.isOpen_mono (H₁ := (Y.delU i A M).ker) (fun g hg => ?_) (Y.delU_open i A M)
    refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
    rw [hco, MonoidHom.mem_ker.1 hg]
    rfl
  have hanti : AntiHom X.cc φ := fun g g' hg => by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_inv, hco, hco, Y.delU_anti i A M g g' hg, toAdd_inv]
    rfl

  have hpair : ∀ x ∈ ({PP, P'} : Finset (Pl D.host.E)), ∀ y, IsConjPl D.host x y → y ∈ ({PP, P'} : Finset (Pl D.host.E)) := by
    intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [GlobalTheory.GalChar.isConjPl_unique hy hc]; simp
    · rw [Finset.mem_singleton] at hx
      subst hx
      rw [GlobalTheory.GalChar.isConjPl_unique hy (GlobalTheory.GalChar.isConjPl_symm hc)]; simp
  have hsub : ({PP, P'} : Finset (Pl D.host.E)) ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hPA
    · rw [Finset.mem_singleton] at hx; subst hx; exact hP'A
  have hunr : ∀ v : Pl D.host.E, v ∉ ({PP} : Finset (Pl D.host.E)) →
      (∀ P ∈ ({PP} : Finset (Pl D.host.E)), ¬ IsConjPl D.host P v) →
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1 := by
    intro v hv hnc B hB σ hσ
    have hv' : v ∉ ({PP, P'} : Finset (Pl D.host.E)) := by
      intro h
      rcases Finset.mem_insert.1 h with rfl | h
      · exact hv (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton] at h
        subst h
        exact hnc PP (Finset.mem_singleton_self _) hc
    refine Multiplicative.toAdd.injective ?_
    rw [hco, ← Y.delU_res i M {PP, P'} A hsub hpair hAconj σ PP (by simp),
      Y.delU_unr i {PP, P'} M v hv' B hB σ hσ]
    rfl
  have hl : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact (hadm.1 P (by simp)).2
  have hg := GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc (Multiplicative (ZMod (X.l i ^ M))) φ (X.l i) (X.lPrime i).out hord hopen
    hanti {PP} (hsplit.mono (Finset.singleton_subset_iff.2 hPP)) hl hunr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  refine ⟨h1, h2, h3, h4, h5, fun P hP => ?_⟩
  rw [Finset.mem_singleton] at hP
  subst hP
  exact h6 _ (Finset.mem_singleton_self _)

end GlobalTheory.UnivGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_transfer_along_surjection_preimage : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H), Function.Surjective ψ → (∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0) → ∀ (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ), (∀ x, ∀ k ∈ K, a (x * k) = a x) → (Function.support fun d : H ⧸ K => a d.out).Finite → (∀ x, ∀ u ∈ U0, β (x * u) = β x) → (∀ t : T, φ' (ψ t) = lam (β t)) → ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0, if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  first | exact @GlobalTheory.cosetSum_transfer_surj | exact GlobalTheory.cosetSum_transfer_surj | (intros; apply GlobalTheory.cosetSum_transfer_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianEqIffSiegelParabolicCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagSame

open GlobalTheory.RawLift GlobalTheory.SWLagTerms GlobalTheory.Doubling

variable {D : D7}

theorem gram_conjT (W : HSp D) : W.gramᴴ = W.gram :=
  Matrix.ext fun i j => W.herm.eq (W.frame j) (W.frame i)

theorem gram_det_unit (W : HSp D) : IsUnit W.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin W.rank → D.host.E, W.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • W.frame j = 0 := by
      apply W.nondeg.2
      intro x
      rw [← W.frame.sum_repr x]
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd D.host.E) (W.frame.repr x i) * ∑ j, W.hT (W.frame i) (W.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 W.frame.linearIndependent v h0 j
  intro a b hab
  exact sub_eq_zero.1 (key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self]))

theorem hAdj_eq (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W M = W.gram⁻¹ * Mᴴ * W.gram := rfl

theorem hAdj_mul (W : HSp D) (M N : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W (M * N) = hAdj W N * hAdj W M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W.gram W.gram⁻¹, Matrix.mul_nonsing_inv _ (gram_det_unit W), Matrix.one_mul]

theorem hAdj_hAdj (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : hAdj W (hAdj W M) = M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjT,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (gram_det_unit W), Matrix.nonsing_inv_mul _ (gram_det_unit W),
    Matrix.mul_one]

def rowD₁ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₁ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₁

def rowD₂ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₂ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₂

theorem frameOf_eq (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    frameOf W g = (hAdj W (rowD₂ W g), hAdj W (rowD₁ W g)) := rfl

theorem blk_mul (W : HSp D) (h g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.SWLagTerms.blk W (h * g) = GlobalTheory.SWLagTerms.blk W h * GlobalTheory.SWLagTerms.blk W g := by
  simp only [GlobalTheory.SWLagTerms.blk, Matrix.submatrix_mul_equiv]

section Blocks

variable {K : Type} [Field K] {r : ℕ}

theorem toBlocks_mul_parts (X Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ + X.toBlocks₁₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₁₂ = X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂ ∧
    (X * Y).toBlocks₂₁ = X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₂₂ = X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
      Fintype.sum_sum_type]

theorem keeps_iff_common (H G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hG : IsUnit G.det) :
    H.toBlocks₂₁ + H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ ↔
      ∃ Q, (H * G).toBlocks₁₁ - (H * G).toBlocks₂₁ = Q * (G.toBlocks₁₁ - G.toBlocks₂₁) ∧
        (H * G).toBlocks₂₂ - (H * G).toBlocks₁₂ = Q * (G.toBlocks₂₂ - G.toBlocks₁₂) := by
  obtain ⟨e11, e12, e21, e22⟩ := toBlocks_mul_parts H G
  rw [e11, e12, e21, e22]
  constructor
  · intro kd
    have h22 : H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ - H.toBlocks₂₁ := by rw [← kd]; abel
    refine ⟨H.toBlocks₁₁ - H.toBlocks₂₁, ?_, ?_⟩ <;> rw [h22] <;> noncomm_ring
  · rintro ⟨Q, h1, h2⟩
    set X := H.toBlocks₁₁ - H.toBlocks₂₁ - Q
    set Y := H.toBlocks₂₂ - H.toBlocks₁₂ - Q
    have hm : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 * G = 0 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
      rw [Matrix.fromBlocks_multiply]
      have a1 : X * G.toBlocks₁₁ + -Y * G.toBlocks₂₁ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring
      have a2 : X * G.toBlocks₁₂ + -Y * G.toBlocks₂₂ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h2; rw [← neg_eq_zero, ← h2]; noncomm_ring
      rw [a1, a2]
      simp
    have h0 : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 = 0 := by
      have := Matrix.mul_nonsing_inv_cancel_right G (Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0) hG
      rw [hm, Matrix.zero_mul] at this
      exact this.symm
    rw [← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
    have hX : X = 0 := h0.1
    have hY : Y = 0 := neg_eq_zero.1 h0.2.1
    have e1 : H.toBlocks₁₁ = H.toBlocks₂₁ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hX)
    have e2 : H.toBlocks₂₂ = H.toBlocks₁₂ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hY)
    rw [e1, e2]; abel

end Blocks

theorem lag_eq_iff (W : HSp D) {Y Y' : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hY : IsLagFrame W Y C) (hY' : IsLagFrame W Y' C') :
    Y = Y' ↔ ∃ B, C'.1 = C.1 * B ∧ C'.2 = C.2 * B := by
  have hcol : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E)
      (B : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (j : Fin W.rank),
      ((fun a => (C.1 * B) a j), (fun a => (C.2 * B) a j)) = ∑ k, B k j • ((fun a => C.1 a k), (fun a => C.2 a k)) := by
    intro C B j
    ext a <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]
  constructor
  · rintro rfl
    have hmem : ∀ j, ((fun a => C'.1 a j), (fun a => C'.2 a j)) ∈
        Submodule.span D.host.E (Set.range fun k => ((fun a => C.1 a k), (fun a => C.2 a k))) := by
      intro j
      rw [IsLagFrame] at hY hY'
      rw [hY, ← hY']
      exact Submodule.subset_span ⟨j, rfl⟩
    choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 (hmem j)
    refine ⟨Matrix.of fun k j => c j k, ?_, ?_⟩
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.1 a) (hc j)
      simp [Prod.fst_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.2 a) (hc j)
      simp [Prod.snd_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
  · rintro ⟨B, h1, h2⟩
    have hle : Y'.1 ≤ Y.1 := by
      rw [IsLagFrame] at hY hY'
      rw [← hY, ← hY', Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [h1, h2]
      rw [hcol]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (Y'.2.1.trans Y.2.1.symm)).symm

theorem frame_iff (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (∃ B, (frameOf W g').1 = (frameOf W g).1 * B ∧ (frameOf W g').2 = (frameOf W g).2 * B) ↔
      ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  simp only [frameOf_eq]
  constructor
  · rintro ⟨B, h1, h2⟩
    refine ⟨hAdj W B, ?_, ?_⟩
    · rw [← hAdj_hAdj W (rowD₁ W g'), h2, hAdj_mul, hAdj_hAdj]
    · rw [← hAdj_hAdj W (rowD₂ W g'), h1, hAdj_mul, hAdj_hAdj]
  · rintro ⟨Q, h1, h2⟩
    exact ⟨hAdj W Q, by rw [h2, hAdj_mul], by rw [h1, hAdj_mul]⟩

theorem keeps_iff_rows (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : IsUnit g.det) :
    KeepsDiag finSumFinEquiv (g' * g⁻¹) ↔ ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  have hb : IsUnit (GlobalTheory.SWLagTerms.blk W g).det := by
    rw [GlobalTheory.SWLagTerms.blk, Matrix.det_submatrix_equiv_self]; exact hg
  have := keeps_iff_common (GlobalTheory.SWLagTerms.blk W (g' * g⁻¹)) (GlobalTheory.SWLagTerms.blk W g) hb
  rw [← blk_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hg] at this
  exact this

theorem keeps_map_iff {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) (hf : Function.Injective f) {n ι : Type}
    (e : n ⊕ n ≃ ι) (M : Matrix ι ι K) : KeepsDiag e (M.map f) ↔ KeepsDiag e M := by
  rw [GlobalTheory.Doubling.keepsDiag_iff e, GlobalTheory.Doubling.keepsDiag_iff e]
  simp only [Matrix.map_apply, ← map_add, hf.eq_iff]

theorem sameClass : ∀ (D : D7) (W : HSp D) (γ γ' : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) (g₀' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ' = g₀'.map (incA D) → ∀ (Y Y' : Lag W), IsLagFrame W Y (frameOf W g₀) → IsLagFrame W Y' (frameOf W g₀') → (Y = Y' ↔ γ' * γ⁻¹ ∈ GlobalTheory.Doubling.siegel W) := by
  intro D W γ γ' g₀ g₀' hγ hγ' Y Y' hY hY'
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  haveI := hinj.nontrivial
  have hu : IsUnit (g₀.map (incA D)).det := by
    rw [← hγ, ← Matrix.isUnit_iff_isUnit_det]
    exact (matHom (GlobalTheory.Doubling.dblSp W) γ).isUnit
  have hg₀ : IsUnit g₀.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h := hu
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h
    exact not_isUnit_zero h
  have h1 : mt _ γ⁻¹ * mt _ γ = 1 := by
    show (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val * (matHom (GlobalTheory.Doubling.dblSp W) γ).val = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : (g₀⁻¹).map (incA D) * g₀.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg₀, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hγ] at h1
  have hinv : mt _ γ⁻¹ = (g₀⁻¹).map (incA D) := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (mt _ γ⁻¹) hu, h1, ← h2, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  have hmt : mt _ (γ' * γ⁻¹) = (g₀' * g₀⁻¹).map (incA D) := by
    rw [Matrix.map_mul, ← hγ', ← hinv]
    show (matHom (GlobalTheory.Doubling.dblSp W) (γ' * γ⁻¹)).val = (matHom (GlobalTheory.Doubling.dblSp W) γ').val * (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val
    rw [map_mul, Units.val_mul]
  rw [lag_eq_iff W hY hY', frame_iff, ← keeps_iff_rows W g₀ g₀' hg₀, ← keeps_map_iff (incA D) hinj, ← hmt]
  exact GlobalTheory.Doubling.mem_siegelOf.symm

end GlobalTheory.SWLagSame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmallStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  first | (exact @GlobalTheory.SchurNear.blocks_small) | (exact GlobalTheory.SchurNear.blocks_small) | (intros; apply GlobalTheory.SchurNear.blocks_small <;> assumption)
end

