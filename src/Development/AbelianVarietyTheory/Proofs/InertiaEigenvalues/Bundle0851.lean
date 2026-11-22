import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0839
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

theorem datP_ne_zero_unpack {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ea : AE D)
    (y : WO (Vc D i) (Wc D i)) (h : datP R i t ea y ≠ 0) :
    IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) ∧
    (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) ∧
    (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) := by
  unfold datP at h
  split_ifs at h with hc
  · refine ⟨hc.2, fun PP hPP => ?_, fun PP hPP => ?_⟩
    · have hK := left_ne_zero_of_mul h
      unfold omegaK at hK
      split_ifs at hK with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hK
    · have hQ := right_ne_zero_of_mul h
      unfold omegaQ at hQ
      split_ifs at hQ with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hQ
  · exact absurd rfl h

theorem disj_supp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hFP i t ea hea P hP e f hpe k hk hkn x x' hxx h1 h2
  apply hkn
  have hPS : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨heP, hfe, hcf, hinf, hcP⟩ := GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split D P e f ea (R.Pg ∪ R.Q t) hpe hea hPS
  obtain ⟨hI1, hK1, hQ1⟩ := datP_ne_zero_unpack R i t ea _ h1
  obtain ⟨hI2, hK2, hQ2⟩ := datP_ne_zero_unpack R i t ea _ h2
  have hY := GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) k x
  have hid := GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split D (Vc D i) (Wc D i) (R.βV i) (R.βW i) f hcf k hk x x' hxx
  rw [← hY] at hid

  have he1 := GlobalTheory.StdFrames.cpt_of_isIdemAt heP
  have hcPP : GlobalTheory.IdemSupport.cP P ≠ P := hcP P hPS
  have hfP : GlobalTheory.StdFrames.cpt P (toEAf D f) = 1 := by
    rw [hfe, RingHom.map_add, GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add, he1.1,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ hcPP), add_zero]
  have hfoff : ∀ PP ∈ R.Pg, PP ≠ P → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 := by
    intro PP hPP hne
    rw [hfe, RingHom.map_add, GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add, he1.2 _ hne,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ (hcP PP (Finset.mem_union_left _ hPP))), add_zero]
  have hu : ∀ (y : WO (Vc D i) (Wc D i)), (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) →
      (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) →
      IsUnit (topL (Wc D i).rank (redM P (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det := by
    intro y hK hQ
    rcases hP with hP | hP
    · rw [hK P hP, Matrix.det_one]; exact isUnit_one
    · exact hQ P hP
  obtain ⟨hint, hdet, hone⟩ := GlobalTheory.T.localFrameChange_mem_integralGL_at_place D P _ _ _ _ _ _ hfP hid hI2 hI1 (hu _ hK2 hQ2) (hu _ hK1 hQ1)
  have hSt := GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport D (Wc D i) (R.βW i) (R.ΛW i) (hL.lev.βW i) e f P heP hfe hcPP k hk hint hdet
  have hred : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → redFn (R.βW i) PP (finE (Wc D i) k) = 1 := by
    rintro PP (hPP | hPP)
    · change PP ∈ R.Pg at hPP
      refine GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one D (Wc D i) (R.βW i) k PP hSt ?_
      by_cases hPe : PP = P
      · subst hPe
        exact hone (hK2 PP hPP) (hK1 PP hPP)
      · intro a b
        rw [GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent D (Wc D i) (R.βW i) f k PP hk (hfoff PP hPP hPe) a b, map_zero]
        exact zero_lt_one
    · exact absurd hPP (Finset.notMem_empty _)
  exact ⟨GlobalTheory.IdemSupport.mem_GfC_of_suppF (Wc D i) hinf hk,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv) _ (GlobalTheory.LevSplit.finE_mem_UA _ k) hSt hred⟩

end GlobalTheory.BadPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

local macro:max "kc% " e:term:max : term => `((by kexactB $e))

namespace GlobalTheory.TwInputs.Move.TieUp

theorem rds_eq {D : D7} {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} {rd : Rds D.nexp ρ} {rd' : Rds (overD D r).nexp (setupUp r ρ)}
    (hr : RdRel h rd rd') : rd' = (rd) := by
  funext i j b
  refine LinearMap.ext fun f => ?_
  have h1 := hr ((i)) i ((HEq.refl i)) ((j)) b ((f))
  refine eq_of_heq ?_
  exact (h1)

theorem tie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good)
    (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ T : Comparison₂ hρ rd,
    ∃ T' : Comparison₂ hρ' rd', ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
      HEq (T i j b).rdV (T' i' (h.cm j) b).rdV := by
  intro D D' ι e h ρ ρ' hs hρ hρ' rd rd' hr T
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  have hrd := rds_eq h hr
  subst hrd
  refine ⟨fun i j b => (cellUp r h hρ' (T i j b)), fun i i' hi j b => ?_⟩
  cases hi
  exact (cellUp_rdV r h hρ' (T i j b))

end GlobalTheory.TwInputs.Move.TieUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlacesGood

variable {D : D7}

theorem over_pde_of_mem_pD (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h : P ∈ (D.ntw.pD i : Set (Pl D.host.E)) := hP
  rw [D.ntw.pD_eq i] at h
  split_ifs at h
  · exact ⟨_, Or.inr rfl, h⟩
  · exact ⟨_, Or.inl rfl, h⟩

theorem natCast_mem_of_conj {P P' : Pl D.host.E} (h : IsConjPl D.host P P') {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal :=
  (h (n : 𝓞 D.host.E) (n : 𝓞 D.host.E) (by simp)).1 hn

theorem splitsC_of_primesOver {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
  have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
  rw [h] at e
  exact e

theorem coprime_of_level {p : ℕ} (hp : p.Prime) (hs : p ∉ D.host.small) (hq : p ≠ D.host.q) (hl : p ∈ D.host.levelPrimes) :
    Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p :=
  Nat.Coprime.mul_left (UpperTheory.Ram.coprime_QSq D.host hp hs hq)
    (D.host.ccK_coprime p (by simp [hl]))

theorem count_AA_eq_zero {P : Pl D.host.E} {p : ℕ} (hc : Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p)
    (hp : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : FractionalIdeal.count D.host.E P D.host.AA = 0 :=
  GlobalTheory.HalfCompare.primeToAA_of_not_mem (GlobalTheory.HalfCompare.not_mem_of_coprime P hc hp)

theorem placesOK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL hsp hq i ch hch
  classical
  have hPg : ∀ P ∈ Rl.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Rl.C.P.Div k P := fun P hP => by
    obtain ⟨k, hk⟩ := (hL.Pg P).1 hP
    exact ⟨k, GlobalTheory.Mem.TypePl.div_over Rl.C.P hk, hk⟩
  have hQ : ∀ P ∈ half ch (D.ntw.pD i), ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => over_pde_of_mem_pD i (mem_half.1 hP).1
  have hsm : ∀ p : ℕ, p.Prime → GlobalTheory.Mem.Chr.SplitsC D.host.E p → p ∉ D.host.small := fun p hp h hs =>
    UpperTheory.Ram.not_dvd_condN_of_unram D.host hp (fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p hp h w hw).2.1)
      (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  have hpp : ∀ p, (p = D.host.pde ∨ p = D.host.pde') → p.Prime ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E p ∧
      Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p ∧ ∀ k, p ≠ D.host.g k := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, splitsC_of_primesOver D.host.pde_prime hsp.1,
        coprime_of_level D.host.pde_prime (hsm _ D.host.pde_prime (splitsC_of_primesOver D.host.pde_prime hsp.1)) hq.1 D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1⟩
    · exact ⟨D.host.pde'_prime, splitsC_of_primesOver D.host.pde'_prime hsp.2,
        coprime_of_level D.host.pde'_prime (hsm _ D.host.pde'_prime (splitsC_of_primesOver D.host.pde'_prime hsp.2)) hq.2 D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2⟩
  refine ⟨⟨Rl.Pg ∪ half ch (D.ntw.pD i), Finset.subset_union_left, Finset.subset_union_right, ?_⟩, ?_, ?_⟩
  · refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => ?_) fun P hP P' hP' hc => ?_
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨k, hk, -⟩ := hPg P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
    · rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨k, hk, hd⟩ := hPg P hP
        obtain ⟨k', hk', hd'⟩ := hPg P' hP'
        have e := GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (D.host.g_prime k) (D.host.g_prime k') (natCast_mem_of_conj hc hk) hk'
        have hkk : k = k' := by
          have := D.host.g_ne
          fin_cases k <;> fin_cases k' <;> simp_all
        subst hkk
        exact GlobalTheory.Mem.TypePl.not_isConjPl Rl.C.P (D.nd.g_split k) hd hd' hc
      · obtain ⟨k, hk, -⟩ := hPg P hP
        obtain ⟨p, hp, hm⟩ := hQ P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) hm (natCast_mem_of_conj hc hk))
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        obtain ⟨k, hk, -⟩ := hPg P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) (natCast_mem_of_conj hc hm) hk)
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        have hs := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
        exact (hch.pair P P' hc (ne_of_split hs hc)).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    obtain ⟨k, hk, -⟩ := hPg P hP
    obtain ⟨p, hp, hm⟩ := hQ P hP'
    exact (hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P (hpp p hp).1 (D.host.g_prime k) hm hk)
  · intro PP hPP PP' hPP'
    have hmem : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := fun n hn => by
      rcases hPP' with rfl | hc
      · exact hn
      · exact GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc hn
    rcases hPP with hPP | hPP
    · obtain ⟨k, hk, -⟩ := hPg PP hPP
      exact count_AA_eq_zero (GlobalTheory.CoverHalf.g_coprime D k).symm (hmem _ hk)
    · obtain ⟨p, hp, hm⟩ := hQ PP hPP
      exact count_AA_eq_zero (hpp p hp).2.2.1 (hmem _ hm)

end GlobalTheory.SeriesTie.PlacesGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStabAll

open Classical GlobalTheory.TwistDetStab

variable {D : D7}

theorem exists_finUnit_isDetRoot {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {k : GA D V} (hk : k ∈ GfC V)
    (hst : Lev.finE V k ∈ St β) : ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ IsDetRoot V k x := by
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hst
  have hd : finPart D (mt V k).det ∈ intAE D := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (ha ▸ a.2)
  have hw : (finHom V k).1.det - 1 ∈ intAE D :=
    sub_mem (hdet ▸ hd) (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (_root_.mul_one _))
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ _ hw (one_nsmul _).symm hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

theorem chi_detAt {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    {β : GL (Fin V.rank) (Lev.EAf D)} {κ : GA D V} (hst : Lev.finE V κ ∈ St β) (he : idem t.Q * idem t.Q = idem t.Q) :
    t.chi (GlobalTheory.VecInv.detAt (idem t.Q) he V κ) =
      ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (ht.split.isIdemAt hP).1.1
  have hsplit : GlobalTheory.VecInv.detAt (idem t.Q) he V κ =
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.coe_prod]
    show idem t.Q * (mt V κ).det + (1 - idem t.Q) = ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _)]
  rw [hsplit, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (ht.split.isIdemAt P.2)).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

def offUnit {R : Type} [CommRing R] (f : R) (hf : f * f = f) (x : Rˣ) : Rˣ where
  val := f + (1 - f) * x.val
  inv := f + (1 - f) * (x⁻¹).val
  val_inv := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf
  inv_val := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf

theorem cmRing_idempotent_unitRatio_identity {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ z, c (c z) = z) (e d x : R) (h1 : e * e = e)
    (h2 : e * c e = 0) (hd : c d * d = 1) (hx : x = d * c x) :
    (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) =
      d * c ((e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have k : (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) = e * d + c e + (1 - (e + c e)) * x := by
    linear_combination (d - 1) * (1 - x) * (h1 + h2)
  rw [k]
  simp only [map_add, map_mul, map_sub, map_one, hc]
  linear_combination (1 - (e + c e)) * hx - c e * hd

theorem finPart_off_mem (f y : AE D) (hf : f * f = f) (hy : finPart D y ∈ intAE D) :
    finPart D (f + (1 - f) * y) ∈ intAE D := by
  have h1 : finPart D f ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hf])
  have h2 : finPart D (1 - f) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul]; congr 1; linear_combination hf)
  rw [RingHom.map_add, RingHom.map_mul]
  exact add_mem h1 (GlobalTheory.HeckeConj.mul_mem_intAE D h2 hy)

theorem detChar_eq_prod_res_of_frame {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    (β : GL (Fin V.rank) (Lev.EAf D)) {κ : GA D V} (hκ : κ ∈ GfC V) (hst : Lev.finE V κ ∈ St β) :
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx⟩ := exists_finUnit_isDetRoot hκ hst
  have he : idem t.Q * idem t.Q = idem t.Q := idem_mul_self ht.split
  have hce : idem t.Q * cA D (idem t.Q) = 0 := ht.split.isIdemSum.2
  have hcc : cA D (idem t.Q) * cA D (idem t.Q) = cA D (idem t.Q) := by rw [← RingHom.map_mul, he]
  have hf : (idem t.Q + cA D (idem t.Q)) * (idem t.Q + cA D (idem t.Q)) = idem t.Q + cA D (idem t.Q) := by
    linear_combination he + hcc + 2 * hce
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem t.Q) he V κ * offUnit _ hf x) :=
    cmRing_idempotent_unitRatio_identity (cA D) GlobalTheory.DualPairCheck.cA_cA (idem t.Q) (mt V κ).det x he hce (det_conj_mul V κ) hx
  have hw : t.chi (offUnit _ hf x) = 1 := by
    refine ht.unram _ ?_ (finPart_off_mem _ _ hf hx2) (finPart_off_mem _ _ hf hx3) ?_
    · show infPart D (_ + (1 - _) * (x : AE D)) = 1
      rw [RingHom.map_add, RingHom.map_mul, hx1, RingHom.map_sub, RingHom.map_one]
      ring
    · show (idem t.Q + cA D (idem t.Q)) * ((idem t.Q + cA D (idem t.Q)) + (1 - (idem t.Q + cA D (idem t.Q))) * (x : AE D)) = _
      linear_combination (1 - (x : AE D)) * hf
  rw [detChar_eq ht.real hroot, map_mul, hw, _root_.mul_one, chi_detAt t ht hst he]

theorem detChar_eq_prod_res : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A),
    t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT →
    detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) :=
  fun B _ _ _ t ht _ hκ hst => detChar_eq_prod_res_of_frame t ht B.F.βT hκ hst

end GlobalTheory.TwistDetStabAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCardStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  first | exact @GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | exact GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | (intros; apply GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NQ

theorem relay_and_arc_inputs : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨_, _, p3, p4, p5, _, _, _, p9, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨_, _, hW1, _, _, hH, hTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨hSat, _, _, _, _, _, _, hF1, _, hF2, _⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,
    ⟨p3, p4, p5, p9, hH, hTr, hW1, hSat⟩⟩

end GlobalTheory.NQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorInvCentralFlipInvariantFormEqStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | exact GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | (intros; apply GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationPreservesNormStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_preserves_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  first | exact @GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | exact GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | (intros; apply GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm <;> assumption)
end

