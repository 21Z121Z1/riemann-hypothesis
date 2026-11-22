import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Formalism.FockGram.SymGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {D : D7}

theorem hasTypeAll_const_mul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {Lie Gs : Set (Mx n)} {f : Mx n → ℂ} (c : ℂ) (h : HasTypeAll Lie Gs σ f) :
    HasTypeAll Lie Gs σ fun g => c * f g := by
  obtain ⟨v, h1, ℓ, hℓ, ⟨S, C, hS, h2, h3, B, hB, hc⟩, h4⟩ := hasTypeAll_iff.1 h
  refine hasTypeAll_iff.2 ⟨v, h1, fun i => c • ℓ i, fun i => GlobalTheory.MultMem.sobCont_smul c (hℓ i),
    ⟨S, fun i => ‖c‖ * C i, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, hc⟩, fun g hg => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i w hw) (norm_nonneg c)
  · simpa only [mul_assoc] using (h3 S' hS').mul_left ‖c‖
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using (h4 g hg).mul_left c

def TypedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹))
    fun g => φ (x * atTau θ V τ g)

theorem isTypeAt_of_typedBy (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {φ : GA D V → ℂ} (h : TypedBy θ M τ φ) : IsTypeAt θ V τ (S τ) φ :=
  ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, M.ds τ, M.fr_unit τ, M.fr_gram τ, fun x => hasTypeAll_iff.1 (h x)⟩

theorem typedBy_value (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar}
    (M : DSModel V Sp) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (τ : D.what₂.Tau) : TypedBy θ M τ (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  intro x
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  refine GlobalTheory.CuspValueType.hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
  have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
  have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
  show ℓ (M.rep τ g (v τ)) = _
  rw [h2, h1]
  rfl

theorem star_lift_isTypeAt (θ : InfFam D) (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) (z : SmT M)
    (τ : D.what₂.Tau) : IsTypeAt θ V τ (dualPar (S τ)) fun g => star (PiTensorProduct.lift T z g) := by
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨hsm, hmult⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨T', hT'm, hT'⟩ := hmult J χ T hT
  have hT'' := (GlobalTheory.MultMem.mem_mult_iff D θ V _ M' J _ T').1 hT'm
  refine isTypeAt_of_typedBy θ M' τ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    let f' : M'.Vec := fun ρ => ⟨(c ρ).symm (f ρ), (hsm ρ _).2 (by simp)⟩
    have e : (fun g => star (PiTensorProduct.lift T (r • PiTensorProduct.tprod ℂ f) g)) = fun g => star r * T' f' g := by
      funext g
      rw [hT' f' f (fun ρ => by simp [f']) g, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, star_mul']
    rw [e]
    intro x
    exact hasTypeAll_const_mul (star r) (typedBy_value θ hHC M' hT'' f' τ x)
  | add a b ha hb =>
    intro x
    have e : (fun g => star (PiTensorProduct.lift T (a + b) (x * atTau θ V τ g))) =
        fun g => star (PiTensorProduct.lift T a (x * atTau θ V τ g)) + star (PiTensorProduct.lift T b (x * atTau θ V τ g)) := by
      funext g
      rw [map_add, Pi.add_apply, star_add]
    rw [e]
    exact (ha x).add (hb x)

end GlobalTheory.StartCusp

namespace GlobalTheory.StartCusp

open Formalism.IndefR.Mult

variable {D : D7}

theorem isCuspFun_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) : IsCuspFun V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)
  | add a b ha hb =>
    rw [map_add]
    exact GlobalTheory.MultMem.isCuspFun_add (GlobalTheory.EndCusp.isAutFunSm_lift hT a).toIsAutFun
      (GlobalTheory.EndCusp.isAutFunSm_lift hT b).toIsAutFun ha hb

set_option maxHeartbeats 1000000 in

theorem lift_isCuspListed : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h

end GlobalTheory.StartCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.SplitVacAlg

variable {D : D7}

def frameLat (V : HSp D) : Submodule (𝓞 D.host.E) V.V := Submodule.span (𝓞 D.host.E) (Set.range V.frame)

theorem frameLat_isLattice (V : HSp D) : Submodule.IsLattice D.host.E (frameLat V) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [frameLat, Submodule.span_span_of_tower]
    exact V.frame.span_eq

theorem frameLat_unimod (V : HSp D) (hV : V.gram = 1) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (frameLat V) := by
  have key := (Formalism.E.hermDual (𝓞 D.host.E) D.host.E V.V (Fin V.rank) V.hT V.frame
    (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    (fun s => ⟨⟨star (s : D.host.E), s.2.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩)).2
    (1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) (fun i j => by
      have := congrFun (congrFun hV i) j
      simp only [HSpace.gram] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [h]) (by simp)
  exact key.2.2 (by simp)

def stdLatSp (V : HSp D) (hV : V.gram = 1) : HSp D :=
  { V with L0 := frameLat V, standardTuple_isLattice := frameLat_isLattice V, baseLattice_isUnimodular := frameLat_unimod V hV }

example (V : HSp D) (hV : V.gram = 1) : GA D (stdLatSp V hV) = GA D V := rfl

theorem mem_frameLattice_iff_integral_coords (V : HSp D) (hV : V.gram = 1) (y : Fin V.rank → D.host.E) :
    y ∈ L0c D (stdLatSp V hV) ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i := by
  change ∑ i, y i • V.frame i ∈ frameLat V ↔ _
  rw [frameLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    have h1 : ∑ i, ((c i : D.host.E)) • V.frame i = ∑ i, y i • V.frame i := by
      rw [← hc]
      exact Finset.sum_congr rfl fun i _ => (algebraMap_smul D.host.E (c i) (V.frame i))
    have := congrArg (fun z => V.frame.repr z i) h1
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  · intro h
    choose c hc using h
    refine ⟨c, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← hc i]
    exact (algebraMap_smul D.host.E (c i) (V.frame i)).symm

end GlobalTheory.SplitVacAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPairWeilLatticeIffStandardOfHalf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem locPl_over {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.1 hw with hw0 | hwQ
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw0
    exact Or.inl ((G.pl.under_w hv).symm ▸ hv)
  · exact Or.inr ⟨w, hwQ, rfl⟩

private theorem kill_lemma' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}
    (N : Std G Set.univ) {t : T} {e : AE D} (he : IsIdemSum e (locPl G t)) (p : Pair T) {X : Node}
    (hX : DefNode D.R.m X) : ∃ a : AE D, e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 :=
  exists_kill N (Set.mem_univ t) (FinDatum.ind G t p (locPl G t) (locPl_over G t) e he) hX

theorem mem_pairLat_iff_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  intro D T L sc G W S t p hp e he x hx
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hXS : DefNode D.R.m (.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
    have hXT : DefNode D.R.m (.grid i D.R.m) := ⟨by omega, rfl⟩
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.chi i D.R.m) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.chi i D.R.m) hXT
    refine (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) D.R.m)).1) (S.N.u (.grid i D.R.m)).1
      ?_ ?_ hT1 hT2 ha hb ?_ hhb hx).symm
    · intro v hv
      have h := hS1 v hv
      rw [← mt_negGA] at h
      exact h
    · intro v hv
      have h := hS2 v hv
      rw [← mt_negGA, map_inv] at h
      exact h
    · unfold SuppAt at hga ⊢
      rw [← mt_negGA] at hga
      exact hga
  | top t' j =>
    have hXS : DefNode D.R.m (.top j) := by simp only [DefPair] at hp; show j ≤ D.R.m; omega
    have hXT : DefNode D.R.m (.top (j + 1)) := hp
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.top t' j) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.top t' j) hXT
    exact (mem_latO_iff_of_half _ _ hS1 hS2 hT1 hT2 ha hb hga hhb hx).symm
  | mu _ _ _ => exact hp.elim
  | core _ => exact hp.elim

end GlobalTheory.StdHalfLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaEx

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

set_option maxHeartbeats 1000000 in

theorem mem_splitOff_of_suppSplit : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  classical
  intro D V Q s hs
  obtain ⟨g, hg⟩ := s
  let P : GA D V → Prop := fun x => ∃ h : x ∈ GfC V, (⟨x, h⟩ : GfC V) ∈ splitOff V Q
  have h1 : P 1 := ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := fun x y ⟨hx, mx⟩ ⟨hy, my⟩ =>
    ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ mx my⟩
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, P (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    refine ⟨GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}, Subgroup.subset_closure ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, ?_, ?_⟩⟩
    · intro q hq v' ε' hε' heq
      have hε : ε' = pairA D.host.F 0 (GlobalTheory.LocalApprox.indA D.host.F {v}) :=
        hinj (heq.symm.trans ((he.2.2).trans (hpl v)))
      obtain ⟨α, hα, hα1, hα0⟩ := hε'
      have hαv : α = GlobalTheory.LocalApprox.indA D.host.F {v} := congrArg Prod.snd (hα.symm.trans hε)
      have hvv : v' = v := by
        by_contra hne
        have := hα0 v (Ne.symm hne)
        rw [hαv, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)] at this
        exact one_ne_zero this
      subst hvv
      intro hqm
      refine hv'.2 ?_
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hk' : ((∏ q ∈ Q, q : ℕ) : 𝓞 D.host.F) = (q : 𝓞 D.host.F) * (k : 𝓞 D.host.F) := by
        rw [hk, Nat.cast_mul]
      rw [hk']
      exact Ideal.mul_mem_right _ _ hqm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ t : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), t ⊆ he2.toFinset →
      P (GlobalTheory.LocalApprox.cutAt V g t) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v t h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  obtain ⟨_, hm⟩ := hgS ▸ key _ subset_rfl
  exact hm

end GlobalTheory.MovedKappaEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearCuspFormFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_cusp_form_family : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  first | exact @GlobalTheory.GKGlobalise.globalise | exact GlobalTheory.GKGlobalise.globalise | (intros; apply GlobalTheory.GKGlobalise.globalise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFifthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_theta_level_fifth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @GlobalTheory.xTypeAutLift | exact GlobalTheory.xTypeAutLift | (intros; apply GlobalTheory.xTypeAutLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairExistenceOfFunctorialityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_existence_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → PairEx := by
  first | exact @GlobalTheory.PairIt.pairEx | exact GlobalTheory.PairIt.pairEx | (intros; apply GlobalTheory.PairIt.pairEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabiliseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | exact GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | (intros; apply GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero <;> assumption)
end

