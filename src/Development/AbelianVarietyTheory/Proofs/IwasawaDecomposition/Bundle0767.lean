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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvalues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.TripRho

open GlobalTheory.TwistedSelmerCompare GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions Formalism.L2.NR

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isRhoOfRow_of_frobEig : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  intro D Rw rowS hRho hGP a σ s hRT hs hj hg hloc hfe
  obtain ⟨hiso, hgood, hspec⟩ := hRho (D.ntw.twOf a) s
  have hjr := D.nd.j_range a
  have hσs : D.what₂.isot (D.nd.j a) (rowS _ s) ≠ ⊥ := by rw [← hj]; exact hiso
  obtain ⟨π', hc', hr', hl', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 (rowS _ s) hσs hgood
  obtain ⟨π'', -, -, hl'', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 σ hg.1 hg.2
  obtain ⟨φ, ι, h1, h2, h3⟩ := hRT
  have h2' : ∀ x : ↥D.LL0, ι (φ ((if D.ntw.side (D.ntw.twOf a) s then D.ntw.emb0 (D.ntw.twOf a)
      else D.ntw.emb0b (D.ntw.twOf a)) x)) = embLL0 D x := by
    intro x; rw [hs]; exact h2 x
  obtain ⟨-, hss, hev⟩ := hspec π' hc' hr' hl' φ ι h1 h2'
  refine ⟨?_, ?_⟩
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    have e1 : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    have e2 : mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
        (D.ntw.rhoS _ s) = mapRep φ (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      rfl
    rw [e1, isSSRep_map_iff]
    rw [e2, isSSRep_map_iff] at hss
    exact hss
  · filter_upwards [hev, D.naut.locG_unr_ae π', D.naut.locG_unr_ae π'', hfe] with w hw hu' hu'' hf hsp
    intro B g hB hg'
    have hR : Rw.locR (rowS _ s) w = Rw.locR σ w := by
      have u1 : D.naut.unr (Rw.locR (rowS _ s) w) := by rw [← hl' w hsp]; exact hu'
      have u2 : D.naut.unr (Rw.locR σ w) := by rw [← hl'' w hsp]; exact hu''
      rw [D.naut.unr_eq_lpUnr _ u1, D.naut.unr_eq_lpUnr _ u2, hf hsp]
    have hpar : D.naut.locG (D.naut.tw π' D.naut.etaTinv) w =
        D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [D.naut.locG_tw, hl' w hsp, hR, hloc w hsp]
    have hcp := hw B g hB hg'
    rw [hpar] at hcp
    refine Eq.trans ?_ hcp
    have hcomp : (iotaO D.nd D.naut a).comp (D.ntw.twist₂ a) =
        ι.toRingHom.comp (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := by
      ext y
      exact (h3 y).symm
    have e1 : ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map (D.ntw.twist₂ a) := rfl
    have e2 : ((mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
          (D.ntw.rhoS (D.ntw.twOf a) s) g : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map
            (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := rfl
    rw [e1, Matrix.charpoly_map, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, ← e2]

end GlobalTheory.TripRho

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
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

namespace GlobalTheory.LevParaLoc

theorem locM_eq_one_of_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s s' : SplitPlace L)
    {κ : GAf L n} (hκ : TrivOutside {s.v} κ) (h : s'.v ≠ s.v) : NX.locM s' κ = 1 :=
  GlobalTheory.LevGChar.locM_triv s' (B := {s.v}ᶜ) (by rwa [compl_compl]) (by simpa using h)

theorem intLift_one {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 1 = 1 := by
  unfold NX.intLift
  rw [dif_pos (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem]
  rfl

theorem intLift_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 0 = 0 := by
  unfold NX.intLift
  rw [dif_pos (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem]
  rfl

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem redMat_one {L : Type} [Field L] [NumberField L] [IsCMField L] {r : ℕ}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) :
    NX.redMat v red (1 : Matrix (Fin r) (Fin r) (v.adicCompletion (maximalRealSubfield L))) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v ((1 : Matrix (Fin r) (Fin r) _) a b)) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, intLift_zero, map_zero]

open Classical in
theorem gVal_one (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  have htop : NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) = 1 :=
    Matrix.submatrix_one _ (Fin.castLE_injective _)
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (NX.glOf_val _ (by simp))
  have hpsi : NX.psiUTot D i b 1 = 1 := by
    unfold NX.psiUTot
    rw [dif_pos (one_mem _)]
    have e : (⟨1, one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [e, map_one, Units.val_one]
  have hd : red (NX.intLift s.v (NX.detT D.R.r
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))))) = 1 := by
    rw [GlobalTheory.LevGChar.detT_one', intLift_one, map_one]
  unfold NX.gVal
  rw [htop, redMat_one, hgl, Pi.mulSingle_one, hpsi, map_one, one_mul]
  split_ifs with h
  · have hu : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
    rw [hu, map_one, Units.val_one, map_one]
  · exact absurd (hd ▸ isUnit_one) h

theorem resRep_one {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    NX.resRep s s.w 1 - 1 ∈ s.w.asIdeal := by
  have hu := GlobalTheory.LevGChar.i_resRep s 1 (map_one _)
  show Valued.v (s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L)) < 1
  have e : s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L) = s.i ((NX.resRep s s.w 1 : 𝓞 L) : L) - 1 := by
    push_cast; rw [map_sub, map_one]
  rw [e]
  exact hu

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem mem_iff (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (P : PlE D.host)
    (hP : P ∈ M.QP ∨ P ∈ M.DP) (hG : ∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v)
    (hQ : ∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (hD : ∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (κ : GAf D.host.E D.R.nV) (hκ : TrivOutside {(M.sp P).v} κ) :
    κ ∈ M.J ↔ NG.ParaRT (M.sp P) D.R.r ((M.sp P).loc _ κ) := by
  have hpar : ((∀ P'' ∈ M.QP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ)) ∧
      (∀ P'' ∈ M.DP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ))) ↔
      NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) := by
    constructor
    · rintro ⟨h1, h2⟩
      rcases hP with h | h
      exacts [h1 P h, h2 P h]
    · intro h
      refine ⟨fun P'' hP'' => ?_, fun P'' hP'' => ?_⟩
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hQ P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hD P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
  have hg : ∀ kv, NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) κ) := fun kv => by
    rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact NX.inLevG_one _ _
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, -, h1, h2⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, (hpar.1 ⟨h1, h2⟩).2⟩
  · rintro ⟨hGL, hll⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, hg,
      hpar.2 ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩⟩

theorem levelPara_loc : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  intro D i j b k Q ψ e₀ W₀ _ _ ρ₀ τ M ek P ξ hP hPn hG hQ hD hψ hδ hξQ hξD
  refine ⟨fun κ hκ => mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ, ?_⟩
  intro κ h hκ u hu
  have hpara := (mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ).1 h
  have hUm : κ ∈ Umax D.host.E D.R.nV := ((M.J_mem κ).1 h).1
  have hx : NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) :=
    ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hpara.1).1 a b, hpara.2⟩
  have hv1 : Valued.v (NX.detT D.R.r (NX.locM (M.sp P) κ)) = 1 :=
    GlobalTheory.LevGChar.i_detT_one _ D.R.r _ (NX.locM (M.sp P) κ⁻¹)
      (by rw [← GlobalTheory.LevGChar.locM_mul, mul_inv_cancel, GlobalTheory.LevGChar.locM_one])
      (fun a b => GlobalTheory.LevGChar.locM_int _ (inv_mem hUm) a b) hx
  have hu' : (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) =
      NX.detT D.R.r (NX.locM (M.sp P) κ) := hu
  have hw : (M.sp P).w = P := M.sp_w P (by rcases hP with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have hclose : Valued.v ((u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) -
      (M.sp P).i ((NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)) : 𝓞 D.host.E) : D.host.E)) < 1 := by
    have := GlobalTheory.LevGChar.i_resRep (M.sp P) _ hv1
    rw [hw] at this
    rw [hu', ← Valuation.map_neg, neg_sub]
    exact this
  have hnm := GlobalTheory.LevGChar.resRep_not_mem (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ))
  have hvu : Valued.v (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by rw [hu']; exact hv1
  have hGp : ∏ kv, NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) κ) = 1 :=
    Finset.prod_eq_one fun kv _ => by rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact gVal_one _ _ _ _ _ _ _ _
  have offQ : ∀ P'' ∈ M.QP, P'' ≠ P → NX.ofOk D i k (NX.tameVal ψ P'' e₀
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hQ P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hψ P'' hP'' _ h1, Units.val_one, map_one]
  have offD : ∀ P'' ∈ M.DP, P'' ≠ P → NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀)
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hD P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hδ P'' hP'' _ h1, Units.val_one, map_one]
  apply Units.ext
  rw [cx_apply, M.chi_eq κ h, hGp, one_mul]
  rcases hP with hPQ | hPD
  · have hPD : P ∉ M.DP := fun h' => hPn ⟨hPQ, h'⟩
    rw [Finset.prod_eq_single_of_mem P hPQ offQ,
      Finset.prod_eq_one (fun P'' hP'' => offD P'' hP'' (fun e => hPD (e ▸ hP''))), mul_one]
    exact (hξQ hPQ u _ hnm hvu hclose).symm
  · have hPQ : P ∉ M.QP := fun h' => hPn ⟨h', hPD⟩
    rw [Finset.prod_eq_single_of_mem P hPD offD,
      Finset.prod_eq_one (fun P'' hP'' => offQ P'' hP'' (fun e => hPQ (e ▸ hP''))), one_mul]
    exact (hξD hPD u _ hnm hvu hclose).symm

end GlobalTheory.LevParaLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlace
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

namespace GlobalTheory.LevChiAt

section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_comp (s : SplitPlace L) :
    s.proj = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom.comp
      (compAt L s.v) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem locM_eq_one (s : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (κ : GAf L n)
    (hκ : TrivOutside {v} κ) (hne : s.v ≠ v) : NX.locM s κ = 1 := by
  have h := hκ s.v (by simpa using hne)
  have e : NX.locM s κ = ((κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)).map
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom := by
    rw [Matrix.map_map, ← RingHom.coe_comp, ← proj_eq_comp]
    rfl
  rw [e, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Gen

variable {D : D7}

section Red
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem intLift_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (1 : v.adicCompletion (maximalRealSubfield L)) = 1 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · exact absurd (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem h

theorem intLift_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    NX.intLift v (0 : v.adicCompletion (maximalRealSubfield L)) = 0 := by
  unfold NX.intLift
  split_ifs with h
  · rfl
  · rfl

theorem redMat_topR_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) {n r : ℕ} (h : r ≤ n) :
    NX.redMat v red (NX.topR h (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))) = 1 := by
  ext a c
  simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
  by_cases hac : a = c
  · subst hac; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne (fun e => hac (Fin.castLE_injective _ e)), Matrix.one_apply_ne hac, intLift_zero, map_zero]

theorem detT_one {R : Type} [CommRing R] (n r : ℕ) : NX.detT r (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold NX.detT
  have : (1 : Matrix (Fin n) (Fin n) R).submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) = 1 := by
    ext a c
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

end Red

theorem gVal_one (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  classical
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 := by
    apply Units.ext
    rw [NX.glOf_val _ (by simp)]
    rfl
  have hpsi : NX.psiUTot D i b (1 : G0g D.nd) = 1 := by
    unfold NX.psiUTot
    rw [dif_pos (Subgroup.one_mem _)]
    have : (⟨1, Subgroup.one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [this, map_one]; rfl
  unfold NX.gVal
  erw [redMat_topR_one, hgl, Pi.mulSingle_one, hpsi, detT_one, intLift_one, map_one red, map_one, one_mul]
  rw [dif_pos isUnit_one]
  have : (isUnit_one : IsUnit (1 : ZMod (D.host.g kv.1))).unit = 1 := Units.ext rfl
  rw [this, map_one]
  exact map_one _

theorem loc_one_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) :
    NX.locM s (1 : GAf L n) = 1 := by
  simp [NX.locM]

theorem chi_eq_at : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ (h : κ ∈ M.J), TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      ((M.χ ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) =
        NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hkv hQ hD κ h hκ
  have hG : ∀ kv, kv ≠ kv0 → NX.locM (M.sp (NX.pG D kv)) κ = 1 := fun kv hne => locM_eq_one _ κ hκ (hkv kv hne)
  have hQl : ∀ P ∈ M.QP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hQ P hP)
  have hDl : ∀ P ∈ M.DP, NX.locM (M.sp P) κ = 1 := fun P hP => locM_eq_one _ κ hκ (hD P hP)
  have h1 := M.chi_eq 1 M.J.one_mem
  have e1 : (⟨1, M.J.one_mem⟩ : M.J) = 1 := rfl
  rw [e1, map_one, Units.val_one] at h1
  simp only [loc_one_eq, gVal_one, Finset.prod_const_one, one_mul] at h1
  rw [M.chi_eq κ h, Fintype.prod_eq_single kv0 (fun kv hne => by rw [hG kv hne, gVal_one]), mul_assoc]
  conv_rhs => rw [← mul_one (NX.gVal D i k b kv0 (M.sp (NX.pG D kv0)) (M.redG kv0) (τ kv0) (NX.locM (M.sp (NX.pG D kv0)) κ))]
  congr 1
  rw [h1]
  congr 1
  · exact Finset.prod_congr rfl fun P hP => by rw [hQl P hP]
  · exact Finset.prod_congr rfl fun P hP => by rw [hDl P hP]

end GlobalTheory.LevChiAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterPsiCondition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

set_option maxHeartbeats 1600000 in

theorem intC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  intro hL hDec hI hT hRT
  refine ((GlobalTheory.T.hecke_reading_eigenvalue_place hL hDec hI hT hRT).and (formsC_at_state hL)).trans
    (StepW.of_all fun K B f T w _ _ H P x hA θ hL' _ hstab hrd => ?_)
  obtain ⟨hB, hF⟩ := H
  intro j k Pl hj1 hj2 hsp hnot hk
  obtain ⟨-, -, Tf, hTf, hMK, hspan⟩ := hF P x hA j hj1 hj2
  obtain ⟨p, hp, hpP, hpN⟩ := GlobalTheory.SupPowNorm.exists_prime_dvd_card Pl
  have hW : ∀ y ∈ ((SOf x).A j).WK, hL' j k Pl y ∈ ((SOf x).A j).WK := fun y hy => hstab j hj1 hj2 k Pl y hy
  obtain ⟨n, hn⟩ := GlobalTheory.SupPowNorm.exists_pow_smul_mem_span ((SOf x).A j) (hL' j k Pl) Tf hTf
    (fun y hy => (hMK y hy).2) hspan hW hp hpN fun la hla g hg hb y =>
      hB P x hA hL' hstab hrd j k Pl hj1 hj2 hsp hnot hk la
        (fun q hq hqP => by rw [GlobalTheory.SupPowNorm.prime_eq_of_mem Pl hq hp hqP hpP]; exact hla) g hg (hW g hg) hb y
  exact ⟨n, fun y hy _ => hn y hy⟩

end GlobalTheory.HeightCounting.RatSide
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  first | exact @GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero | exact GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero | (intros; apply GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsOfLiterature
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem localLanglandsGL_and_prN_of_lit : LitLoc → LitAut → GlobalTheory.Published.LocalLanglandsGL ∧ PrN := by
  intro L A
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.T.local_langlands_of_published L.llc L.conv L.dzc L.dzi L.brauer L.chev A.art L.exh L.multi L.cos L.zel L.geo L.bz
  refine ⟨hL, ?_⟩
  have hG : GlobalTheory.GLq.Green := GlobalTheory.GreenBridge.green_of_regular L.green
  exact
    { what₂ := GlobalTheory.T.published_inputs_combined L.bz L.bern L.geo L.disj L.mp L.theta A.js A.fin A.ctemp L.temp L.seg A.gk A.gal A.car
        A.pur A.coh A.art A.chA A.chW A.berger GlobalTheory.Published.chebotarevDegreeOne' hL
      decay := A.decay
      hc := A.hc
      greenC := hG
      green := hG
      zel := L.zel
      dz := GlobalTheory.T.depth_zero_inertia_of_langlands L.dzt A.art hL
      ray := A.ray
      rayF := A.ray
      rayA := GlobalTheory.Published.GlobalArtinReciprocity.rayCharacterArtin A.art
      bc := GlobalTheory.BaseChangeBridge.main A.bc L.bern
      ds := GlobalTheory.T.discrete_spectrum_of_residual A.mw
      gen := GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos
      std := L.cos
      cheb := GlobalTheory.Published.cheb_holds
      howe := GlobalTheory.Hk3.howeUnram_holds }

end GlobalTheory.Mem.LiteralAutomorphy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.motive_theta_of_read_relation : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → EMtTheta Y (ysL L l) (chD L l) := by
  first | exact @GlobalTheory.HeightCounting.Fin3.emtTheta_L | exact GlobalTheory.HeightCounting.Fin3.emtTheta_L | (intros; apply GlobalTheory.HeightCounting.Fin3.emtTheta_L <;> assumption)
end

