import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0850
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorsTargetLieRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (τ : D.what₂.Tau), ∃ κ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ → ℂ, ∀ Y ∈ lieAt (Wc D i) τ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + κ Y • P) z) 0 := by
  first | exact @GlobalTheory.FockLieW.hasDerivAt_fockVector | exact GlobalTheory.FockLieW.hasDerivAt_fockVector | (intros; apply GlobalTheory.FockLieW.hasDerivAt_fockVector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointHarmonic_highestWeight_multiplicity_one : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  first | exact @GlobalTheory.HarmLine.joint_line | exact GlobalTheory.HarmLine.joint_line | (intros; apply GlobalTheory.HarmLine.joint_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmittedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremA_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  first | exact @GlobalTheory.AdmittedPartOne.all_admitted | exact GlobalTheory.AdmittedPartOne.all_admitted | (intros; apply GlobalTheory.AdmittedPartOne.all_admitted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremCHypothesesAdmittedStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremC_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  first | exact @GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremCAdm.admissible_ranks_of_CMDatum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmittedStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremE_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  first | exact @GlobalTheory.AdmThmE.admitted_all | exact GlobalTheory.AdmThmE.admitted_all | (intros; apply GlobalTheory.AdmThmE.admitted_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen

theorem lowZero_map_iff {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : LowZero k (y.map f) ↔ LowZero k y := by
  unfold LowZero
  simp only [Matrix.map_apply, map_eq_zero_iff f f.injective]

theorem topL_map {A B : Type} [Zero A] [Zero B] (f : A → B) (hf : f 0 = 0) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : topL k (y.map f) = (topL k y).map f := by
  ext i j
  simp only [topL, Matrix.map_apply]
  split_ifs <;> simp [hf]

theorem det_topL_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det := by
  rw [topL_map f (map_zero f), RingHom.map_det]
  rfl

theorem det_topL_mapE {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) {b a : ℕ} (k : ℕ)
    (y : Matrix (Fin b) (Fin a) A) : (topL k (y.map f)).det = f (topL k y).det :=
  det_topL_map (f : A →+* B) k y

theorem omegaQ_single {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : LowZero r (y PP)) (u : (kP PP)ˣ)
    (hu : (u : kP PP) = (topL r (y PP)).det) :
    omegaQ {PP} r ξ (-1) y = ((ξ PP u : ℂˣ) : ℂ)⁻¹ := by
  have h : ∀ PP' ∈ ({PP} : Finset (Pl D.host.E)), LowZero r (y PP') ∧ IsUnit (topL r (y PP')).det := by
    intro PP' hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨hz, hu ▸ u.isUnit⟩
  unfold omegaQ
  rw [dif_pos h, Finset.prod_eq_single ⟨PP, Finset.mem_singleton_self PP⟩]
  · rw [_root_.zpow_neg_one]
    congr 4
    ext
    simp [hu]
  · intro x _ hx
    exfalso
    exact hx (Subtype.ext (Finset.mem_singleton.1 x.2))
  · intro hx
    exact absurd (Finset.mem_attach _ _) hx

theorem omegaQ_ne_zero {D : D7} {a b : ℕ} (PP : Pl D.host.E) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : omegaQ {PP} r ξ k y ≠ 0) :
    LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
  unfold omegaQ at h
  split_ifs at h with h'
  · exact h' PP (Finset.mem_singleton_self PP)
  · exact absurd rfl h

end GlobalTheory.DownLift.ConjHalfGen
end

noncomputable section
namespace GlobalTheory.DownLift.ConjHalfGen

set_option maxHeartbeats 1000000 in

theorem mem_span_translT : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  classical
  intro D S T βS βT hrn ΛS ΛT N hBF hLS hLT e PP hidem ξ hξ Φ hΦ hlaw
  obtain ⟨v, φ, ι, hch⟩ := GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles D e PP hidem
  obtain ⟨hsurj, hinj, hint, hred⟩ := GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι hidem hch
  haveI : Finite (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := Finite.of_equiv _ ι.toEquiv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (GlobalTheory.SplitHecke.Ov D v)
  choose σ hσH hσ using hsurj
  set ω := omegaQ {PP} T.rank ξ (-1) with hω
  set Φ' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => Φ (σ m) with hΦ'
  set Φ₀' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ := fun m => adjDat S T βS βT e ω (σ m) with hΦ₀'
  set ξ' : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ →* ℂˣ :=
    (ξ PP).comp (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom) with hξ'
  have hξ'1 : ξ' ≠ 1 := by
    intro h1
    apply hξ
    ext u
    have h2 := DFunLike.congr_fun h1 (Units.map (ι : kP PP ≃+* _).toMonoidHom u)
    have h3 : Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom
        (Units.map (ι : kP PP ≃+* _).toMonoidHom u) = u := by
      ext; simp
    simp only [hξ', MonoidHom.comp_apply, h3, MonoidHom.one_apply] at h2
    rw [h2]; rfl

  have hA : ∀ (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)) (u : (IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v))ˣ),
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) = (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det →
      Φ₀' (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = ((ξ' u : ℂˣ) : ℂ)⁻¹ := by
    intro z u hz hu
    set x := σ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxH := hσH (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxr := hσ (z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have hxI : IsIntM (frMapAdj S T βS βT x) := (hint x hxH).2 ⟨z, hxr⟩
    have hxR := hred x z hxI hxr
    have hLZ : LowZero T.rank (redM PP (frMapAdj S T βS βT x)) := by
      rw [← lowZero_map_iff ι, hxR]; exact hz
    have hdet : ι (topL T.rank (redM PP (frMapAdj S T βS βT x))).det = (u : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) := by
      rw [hu, ← hxR, det_topL_mapE ι]
    show adjDat S T βS βT e ω x = _
    unfold adjDat
    rw [if_pos ⟨hxH, hxI⟩, hω, omegaQ_single PP T.rank ξ _ hLZ
      (Units.map (ι.symm : IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) ≃+* kP PP).toMonoidHom u)]
    · rfl
    · simp [← hdet]
  have hB : ∀ m, Φ₀' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
      m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) ∧
      LowZero T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) ∧
      IsUnit (topL T.rank (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))).det := by
    intro m hm
    have hm' : adjDat S T βS βT e ω (σ m) ≠ 0 := hm
    unfold adjDat at hm'
    split_ifs at hm' with hc
    · obtain ⟨z, hz⟩ := (hint (σ m) hc.1).1 hc.2
      have hR := hred (σ m) z hc.2 hz
      obtain ⟨h1, h2⟩ := omegaQ_ne_zero PP T.rank ξ (-1) _ hm'
      refine ⟨z, by rw [← hz, hσ], ?_, ?_⟩
      · rw [← hR, lowZero_map_iff ι]; exact h1
      · rw [← hR, det_topL_mapE ι]; exact h2.map _
    · exact absurd rfl hm'

  have hC : ∃ N : ℕ, (∀ m (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)),
      Φ' (m + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v))) = Φ' m) ∧
      ∀ m, Φ' m ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • m = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
    obtain ⟨N', hinv, hsupp⟩ := GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport D S T βS βT e PP v φ ι hidem hch ΛS ΛT hLS hLT Φ hΦ ϖ hϖ
    refine ⟨N', fun m z => ?_, fun m hm => ?_⟩
    · exact hinv (σ m) _ (hσH m) (hσH _) z (by rw [hσ, hσ])
    · obtain ⟨z, hz⟩ := hsupp (σ m) hm
      exact ⟨z, by rw [← hσ m]; exact hz⟩

  have hD : ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), LowZero T.rank (h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v))) →
      ∀ m m' : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v),
      Φ' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m) * Φ₀' m' =
        Φ' m * Φ₀' (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * m') := by
    intro h hLZ m m'
    obtain ⟨κ, hsupp, hGf, hSt, hrκ, hoth, hact⟩ := GlobalTheory.T.exists_unitary_supported_at_split_place_lift D S T βS βT e PP v φ ι hidem hch ΛS N hBF h
    have hBT : redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) := by
      rw [mem_blockTri]
      intro i j hij
      have hj : j.val < T.rank := by
        by_contra hj; simp only [blk2, if_neg hj] at hij; split_ifs at hij <;> omega
      have hi : T.rank ≤ i.val := by
        by_contra hi; simp only [blk2, if_pos (Nat.lt_of_not_le hi)] at hij; omega
      have h1 := congrFun (congrFun hrκ i) j
      simp only [Matrix.map_apply] at h1
      have h4 := hLZ i j hi hj
      simp only [Matrix.map_apply] at h4
      exact ι.injective ((h1.trans h4).trans (map_zero ι).symm)
    have hmove : ∀ y, σ (h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * y) = actO S T κ 1 (σ y) := by
      intro y
      refine hinj _ _ (hσH _) (GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσH y)) ?_
      rw [hσ, hact, hσ]
    show Φ (σ _) * adjDat S T βS βT e ω (σ m') = Φ (σ m) * adjDat S T βS βT e ω (σ _)
    rw [hmove, hmove]
    exact hlaw κ hsupp hGf hSt hBT hoth (σ m) (σ m') (hσH m) (hσH m')
  have hpure := GlobalTheory.T.parahoric_schwartz_mem_span_datum_translates_alt (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) S.rank T.rank hrn ϖ hϖ ξ' hξ'1 Φ' Φ₀' hA hB hC hD

  let L : ((Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun Ψ x => if IsHalf (cA D e) x then Ψ (rdAdj S T βS βT φ x) else 0
      map_add' := fun Ψ Ψ' => by funext x; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c Ψ => by funext x; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hLΦ : L Φ' = Φ := by
    funext x
    show (if IsHalf (cA D e) x then Φ (σ (rdAdj S T βS βT φ x)) else 0) = Φ x
    split_ifs with hx
    · rw [hinj _ x (hσH _) hx (hσ _)]
    · by_contra hne
      exact hx (hΦ.1 x (Ne.symm hne))
  have hmem := Submodule.mem_map_of_mem (f := L) hpure
  rw [Submodule.map_span, hLΦ] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨Ψ, ⟨γ, rfl⟩, rfl⟩
  obtain ⟨g, hgs, hgx⟩ := GlobalTheory.T.exists_supported_unitary_adjoint_action D S T βS βT e PP v φ ι hidem hch γ
  refine ⟨g, ?_, ?_⟩
  · intro i j
    have := hgs i j
    rwa [Formalism.L2.Theta.cA_cA, add_comm]
  · funext x
    show (if IsHalf (cA D e) x then adjDat S T βS βT e ω (σ (rdAdj S T βS βT φ x * γ.val)) else 0) = adjDat S T βS βT e ω (actO S T 1 g x)
    split_ifs with hx
    · have hgH := GlobalTheory.SplitHecke.isHalf_actO 1 g hx
      rw [hinj _ (actO S T 1 g x) (hσH _) hgH (by rw [hσ, hgx])]
    · have hgH : ¬ IsHalf (cA D e) (actO S T 1 g x) := by
        intro h'
        have := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S)⁻¹ g⁻¹ h'
        rw [GlobalTheory.SplitHecke.actO_inv_actO] at this
        exact hx this
      unfold adjDat
      rw [if_neg (fun h' => hgH h'.1)]

end GlobalTheory.DownLift.ConjHalfGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealComponentEqConjInverseRationalMatrixStatement
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
theorem _root_.GlobalTheory.T.realComponent_eq_conj_inverse_rationalMatrix : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E),
    γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → ∀ τ : D.what₂.Tau, ∃ σ : D.host.E →+* ℂ,
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map σ := by
  first | exact @GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv | exact GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv | (intros; apply GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointActsOnThetaFockVacuaByDetPowerStatement
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
theorem _root_.GlobalTheory.T.realPoint_acts_on_thetaFockVacua_by_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  first | exact @GlobalTheory.RealVacPow.vacuum_det_power | exact GlobalTheory.RealVacPow.vacuum_det_power | (intros; apply GlobalTheory.RealVacPow.vacuum_det_power <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem setup_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameSetup ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' :=
  fun h _ _ m ρ g p => setup_move_data h m ρ g p

end GlobalTheory.TwInputs.Move
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExportStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_export : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → GlobalTheory.EigTie.ResTied D Rw → GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D → D.nexp.sig_all → GlobalTheory.Triple.IsTriple D := by
  first | exact @GlobalTheory.TripInhab.isTriple_of_sideB | exact GlobalTheory.TripInhab.isTriple_of_sideB | (intros; apply GlobalTheory.TripInhab.isTriple_of_sideB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenThetaMatch
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty

theorem large_and_duties_of_large_rings : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → BuiltEx A M C tp.tup → EvO A M C tp.tup (fun D' => (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → EvO A M C tp.tup (fun D' => Large D' ∧ Duties D') ∧ ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tp.tup big L ∧ Large (withLoc L) ∧ Duties (withLoc L) := by
  intro hCheb D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx hO
  have hStd : HeckeStdPlain := GlobalTheory.T.heckeDoubleCosetOperators_standardFacts

  have hConj := fun P₁ P₂ => (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup P₁ P₂).1
  have hMono := fun P₁ P₂ => (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup P₁ P₂).2.1

  have E1 : EvO A M C tp.tup SumRepresentations.hypO :=
    GlobalTheory.T.side_eigen_rationality hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh

  have E2 : EvO A M C tp.tup GlobalTheory.SplitCoef.OSplit := by
    obtain ⟨big, hbig⟩ := GlobalTheory.T.side_multiplicity_cusp D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
    refine ⟨big, fun L hB => ?_⟩
    obtain ⟨Sp, ⟨hA⟩, -⟩ := hB
    exact hbig L Sp hA

  have E3 : EvO A M C tp.tup (fun D' => ∀ i, ZDecomp D'.nd i) :=
    hMono _ _ (fun D' h => GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev hCheb D' h.2) hO
  have E4 : EvO A M C tp.tup (fun D' => SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') :=
    hMono _ _ (fun D' h => h.2.1 h.1) (hConj _ _ E1 hO)

  have E5 : EvO A M C tp.tup TakenAll :=
    GlobalTheory.T.side_eigen_hecke_match hCheb hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx
      (hMono _ _ (fun D' h => ⟨h.1.1, h.2.1, h.2.2⟩) (hConj _ _ E4 (hConj _ _ E2 E3)))
  have EL : EvO A M C tp.tup Large :=
    hMono _ _ (fun D' h => ⟨h.1, h.2.1, h.2.2⟩) (hConj _ _ E1 (hConj _ _ E2 E5))
  have ELD : EvO A M C tp.tup (fun D' => Large D' ∧ Duties D') :=
    hMono _ _ (fun D' h => ⟨h.1, GlobalTheory.T.duties_of_large_of_cheb hCheb D' h.1 h.2.1 h.2.2⟩) (hConj _ _ EL E4)
  refine ⟨ELD, fun big₀ => ?_⟩
  obtain ⟨big, L, hsub, hB, hP⟩ :=
    (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup (fun D' => Large D' ∧ Duties D') (fun _ => True)).2.2.1 hEx ELD big₀
  exact ⟨big, L, hsub, hB, hP.1, hP.2⟩

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanFiniteTranslatesVacuumThetaFockVacuaStatement
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
theorem _root_.GlobalTheory.T.span_finiteTranslates_vacuum_thetaFockVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  first | exact @GlobalTheory.LevelSeries.trSp_theta_fock | exact GlobalTheory.LevelSeries.trSp_theta_fock | (intros; apply GlobalTheory.LevelSeries.trSp_theta_fock <;> assumption)
end

