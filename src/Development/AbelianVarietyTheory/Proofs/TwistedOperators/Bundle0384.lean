import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_levi_commutative_noncompact : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) P, IsPar P → ∀ γ : GF V, IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P → IsMulCommutative (cent (rat V γ)) ∧ cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P ∧ (P ≠ ∅ → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w))) := by
  first | exact @GlobalTheory.LeviCent.cent_levi | exact GlobalTheory.LeviCent.cent_levi | (intros; apply GlobalTheory.LeviCent.cent_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  first | exact @GlobalTheory.RowEvalHH.conj_eval_mem_HH | exact GlobalTheory.RowEvalHH.conj_eval_mem_HH | (intros; apply GlobalTheory.RowEvalHH.conj_eval_mem_HH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (P p.1) (Q p.1) (G p.1) p.2) := by
  first | exact @GlobalTheory.HeisOrbit.dOp_contDiff_family | exact GlobalTheory.HeisOrbit.dOp_contDiff_family | (intros; apply GlobalTheory.HeisOrbit.dOp_contDiff_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespond
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreOntoPar
open GlobalTheory.SignedHC GlobalTheory.PairLift Finset

theorem mem_dualPar' {S : SPar} {x : ℚ × Bool} : x ∈ dualPar S ↔ (-x.1, x.2) ∈ S := by
  simp only [dualPar, mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, h, he⟩
    rw [← he]; simpa using h
  · intro h; exact ⟨_, _, h, by simp⟩

theorem mem_block_neg {c y : ℚ} {t : ℕ} : y ∈ TPar.block (-c) t ↔ -y ∈ TPar.block c t := by
  rw [mem_block, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · rintro ⟨a, ha, h⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

theorem dual_partner (t : ℕ) (c : ℚ) (P : SPar) (hc : ∀ x ∈ P, x.1 ≠ c) :
    partner t true (-c) (-c) (dualPar P) = dualPar (GlobalTheory.SignedHC.flip (partner t false c c P)) := by
  ext ⟨y, b⟩
  rw [mem_dualPar', GlobalTheory.SignedHC.mem_flip]
  simp only [partner, mem_union, mem_image, Prod.exists, Prod.mk.injEq, mem_dualPar', sub_neg_eq_add,
    add_neg_cancel_right, sub_add_cancel]
  constructor
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, rfl, rfl⟩)
    · left
      refine ⟨-a, b', h, rfl, ?_⟩
      have hne : -a ≠ c := hc _ h
      by_cases h1 : a < -c
      · have h3 : ¬ (-a < c) := by linarith
        rw [if_pos h1] at h2; rw [if_neg h3]; subst h2; simp
      · have h3 : -a < c := lt_of_le_of_ne (by linarith) hne
        rw [if_neg h1] at h2; rw [if_pos h3]; subst h2; simp
    · right; exact ⟨-a, mem_block_neg.1 ha, rfl, rfl⟩
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, ha', hb⟩)
    · left
      have hne : -y ≠ c := hc _ h
      refine ⟨y, b', h, rfl, ?_⟩
      by_cases h1 : y < -c
      · have h3 : ¬ (-y < c) := by linarith
        rw [if_neg h3] at h2; rw [if_pos h1]; subst h2; simp
      · have h3 : -y < c := lt_of_le_of_ne (by linarith) hne
        rw [if_pos h3] at h2; rw [if_neg h1]; exact Bool.not_inj h2
    · right
      subst ha'
      refine ⟨y, mem_block_neg.2 ha, rfl, ?_⟩
      cases b
      · exact absurd hb (by decide)
      · rfl

theorem parOK_core : ParOK := by
  intro D hS i hi τ
  show GlobalTheory.EvenOnto.UpPair (GlobalTheory.ChiGrid.sLen D - 1) ((GlobalTheory.ChiGrid.num D 1 τ).parPi i) ((GlobalTheory.ChiGrid.num D 1 τ).parPi (i + 1)) _ _
  set G := GlobalTheory.ChiGrid.num D 1 τ with hGdef
  set c : ℚ := (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) : ℚ) with hc
  have hN : G.NearMid := GlobalTheory.ChiGrid.num_nearMid D 1 τ
  have hgp := (GlobalTheory.ChiGrid.isLeast_gap D 1).1
  have hγ : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 + 2 * GlobalTheory.ChiGrid.sLen D + 2 < GlobalTheory.ChiGrid.gap D 1 := hgp.2.1
  have hr := hS.1
  have hsl : GlobalTheory.ChiGrid.sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ G.s := show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega
  have hq : G.s = 2 * (a + b + 2) + 1 := show GlobalTheory.ChiGrid.sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < GlobalTheory.ChiGrid.bigN D := by unfold GlobalTheory.ChiGrid.bigN; omega
  have hγq : (G.s : ℚ) + 4 ≤ G.ga := by
    show (GlobalTheory.ChiGrid.sLen D : ℚ) + 4 ≤ (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : GlobalTheory.ChiGrid.sLen D + 4 ≤ GlobalTheory.ChiGrid.gap D 1)
  have hγ2 : 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < G.ga := by
    show 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 < GlobalTheory.ChiGrid.gap D 1)
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hsγ : (G.s : ℚ) ≤ G.ga := by linarith
  have hsq : (G.s : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) := rfl
  have hcastT : ((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega)]; simp
  have hfar : FarFrom c (((GlobalTheory.ChiGrid.sLen D : ℚ) + 2) / 2) (G.parPi i) :=
    GlobalTheory.ParPairArrows.far_parPi G hN hs1 hγq hi
  have hpart : partner (GlobalTheory.ChiGrid.sLen D - 1) false c c (G.parPi i) = GlobalTheory.SignedHC.flip (G.parPi (i + 1)) :=
    GlobalTheory.ParPairArrows.partner_parPi G hN hs1 hγq hi
  have hcne : ∀ x ∈ G.parPi i, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  have hflip : ∀ S : SPar, GlobalTheory.SignedHC.flip (GlobalTheory.SignedHC.flip S) = S := fun S => by
    ext ⟨x, s⟩; simp [mem_flip]
  have hP1 : partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i)) = dualPar (G.parPi (i + 1)) := by
    rw [dual_partner _ _ _ hcne, hpart, hflip]
  have hgapP : ∀ j, j ≤ D.R.m → GapOver (dualPar (G.parPi j)) (2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3) := by
    intro j hj x hx y hy hne
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hj _ hx _ hy hne
    have e : |(-x.1) - (-y.1)| = |x.1 - y.1| := by rw [show (-x.1) - (-y.1) = -(x.1 - y.1) by ring, abs_neg]
    rw [e] at this
    linarith
  have hne : (dualPar (G.parPi i)).Nonempty := by
    have h0 : (G.parPi i).Nonempty := ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
    exact h0.image _
  have hreg : IsRegular (dualPar (G.parPi i)) := by
    intro x hx y hy e
    by_contra hne'
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hi.le _ hx _ hy hne'
    rw [e, sub_self, abs_zero] at this
    linarith
  have hco : InCoset (-c + (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (entries (dualPar (G.parPi i))) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    obtain ⟨z, hz⟩ := GlobalTheory.ParPairArrows.inCoset_parPi G hq (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) - GlobalTheory.ChiGrid.sLen D) i (-x)
      (fst_mem_entries hs')
    have hcastG : ((G.s - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := hcastT
    rw [hcastG] at hz
    push_cast at hz
    refine ⟨-z, ?_⟩
    rw [hcastT]; push_cast
    linarith
  have hfar' : FarFrom (-c) ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (dualPar (G.parPi i)) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    have := hfar _ (fst_mem_entries hs')
    simp only at this
    have e : |x - -c| = |-x - c| := by rw [show x - -c = -(-x - c) by ring, abs_neg]
    rw [hcastT, e]
    linarith
  have hcard : (dualPar (G.parPi i)).card + (GlobalTheory.ChiGrid.sLen D - 1) ≤ GlobalTheory.ChiGrid.bigN D := by
    have hc0 : (dualPar (G.parPi i)).card ≤ (G.parPi i).card := card_image_le
    have hc := GlobalTheory.ParPairArrows.card_parPi G i
    have h1 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) ≤ D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) = i * (GlobalTheory.ChiGrid.sLen D - 1) + (GlobalTheory.ChiGrid.sLen D - 1) := Nat.succ_mul _ _
    have h3 : D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (GlobalTheory.ChiGrid.sLen D - 1) at hc
    show _ ≤ D.R.k + D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1)
    omega
  have hth := GlobalTheory.PairLift.FromSigned.thetaPar_partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i))
    (GlobalTheory.ChiGrid.bigN D) (by omega) hne hreg hco hfar' hcard hN1 (hgapP i hi.le) (by rw [hP1]; exact hgapP (i + 1) hi)
  obtain ⟨al, be, ga, de, hPe, (⟨hD, hP'⟩ | ⟨_, hP'⟩)⟩ := hth
  · refine ⟨al, be, ga, de, hD, ?_, ?_, ?_⟩
    · intro e he
      have hmem : ∃ s, (e + -c, s) ∈ dualPar (G.parPi i) := by
        rw [hPe]
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
      obtain ⟨s, hs⟩ := hmem
      rw [mem_dualPar'] at hs
      simp only at hs
      have := hfar _ (fst_mem_entries hs)
      simp only at this
      have e1 : |-(e + -c) - c| = |e| := by rw [show -(e + -c) - c = -e by ring, abs_neg]
      rw [e1] at this
      rw [hcastT]
      linarith
    · rw [← hPe, dualPar_dualPar]
    · rw [← hP', hP1, dualPar_dualPar]
  · exfalso
    have hg := hgapP (i + 1) hi
    rw [← hP1, hP'] at hg
    have e0m : (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 ∈ block (GlobalTheory.ChiGrid.sLen D - 1) :=
      GlobalTheory.PairLift.FromSigned.mem_blockList.2 ⟨0, by omega, by simp⟩
    have hf : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, false) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) :=
      GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [e0m]⟩)
    have ht : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, true) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) := by
      rw [← hP']
      refine mem_union.2 (Or.inr (mem_image.2 ⟨_, mem_block.2 ⟨0, by omega, ?_⟩, rfl⟩))
      push_cast; ring
    have := hg _ ht _ hf (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.CoreOntoPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetEigen

theorem heisO_lincomb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) :
    heisO ψ S T y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • heisO ψ S T y (f i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cosetSum_eigen : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  intro D ψ S T ΛS ΛT P e he Λd R x hR h2 h3 h4 g hg y hy hyd
  classical
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm]; exact he.2
  have half_add : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a + b) :=
    fun ha hb i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  have half_neg : ∀ {a : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) (-a) :=
    fun ha i j => by rw [Matrix.neg_apply, mul_neg, ha i j]
  have half_sub : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a - b) :=
    fun ha hb => by rw [sub_eq_add_neg]; exact half_add ha (half_neg hb)
  have ann_add : ∀ {a b : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → (∀ u ∈ Λd, ψ (symplO S T u b) = 1) →
      ∀ u ∈ Λd, ψ (symplO S T u (a + b)) = 1 :=
    fun ha hb u hu => by rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  have ann_neg : ∀ {a : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → ∀ u ∈ Λd, ψ (symplO S T u (-a)) = 1 :=
    fun ha u hu => by rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, ha u hu, inv_one]
  choose! f hfR hfΛ using h2
  have hyz : ∀ z ∈ R, IsHalf (cA D e) (y + z) ∧ ∀ u ∈ Λd, ψ (symplO S T u (y + z)) = 1 := fun z hz =>
    ⟨half_add hy (hR z hz).1, ann_add hyd (hR z hz).2⟩
  have hzy : ∀ z ∈ R, IsHalf (cA D e) (z + -y) ∧ ∀ u ∈ Λd, ψ (symplO S T u (z + -y)) = 1 := fun z hz =>
    ⟨half_add (hR z hz).1 (half_neg hy), ann_add (hR z hz).2 (ann_neg hyd)⟩
  have hfix : ∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a →
      heisO ψ S T a g = g := fun a ha hh =>
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he a ha (Or.inr hh)
  have key : ∀ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T y (heisO ψ S T z g) =
      ψ (symplO S T x y) • (ψ (-symplO S T x (f (y + z))) • heisO ψ S T (f (y + z)) g) := by
    intro z hz
    obtain ⟨hh, ha⟩ := hyz z hz
    have hσR := hfR _ hh ha
    have ha0 := hfΛ _ hh ha
    generalize f (y + z) = s at hσR ha0 ⊢
    have hσh := (hR _ hσR).1
    have ha0h : IsHalf (cA D e) (y + z - s) := half_sub hh hσh
    have e1 : heisO ψ S T y (heisO ψ S T z g) = heisO ψ S T s g := by
      rw [← Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hy (hR z hz).1)]
      have hsplit : y + z = s + (y + z - s) := by abel
      rw [hsplit, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hσh ha0h), hfix _ ha0 ha0h]
    have hlin : symplO S T x y + symplO S T x z = symplO S T x s + symplO S T x (y + z - s) := by
      rw [← Formalism.IndefR.Fin.symplO_add_right, ← Formalism.IndefR.Fin.symplO_add_right]
      congr 1; abel
    have hph : -symplO S T x z = symplO S T x y + -symplO S T x s + -symplO S T x (y + z - s) := by
      linear_combination (-1 : AF D.host.F) * hlin
    rw [e1, hph, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv ψ (symplO S T x (y + z - s)),
      h4 _ ha0 ha0h, inv_one, mul_one, smul_smul]
  rw [heisO_lincomb, Finset.sum_congr rfl key, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun z => f (y + z)) (fun z => f (z + -y)) (fun z hz => hfR _ (hyz z hz).1 (hyz z hz).2)
    (fun z hz => hfR _ (hzy z hz).1 (hzy z hz).2) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl)
  · have hs := hfR _ (hyz z hz).1 (hyz z hz).2
    have h1 := hfΛ _ (hyz z hz).1 (hyz z hz).2
    have h2' := hfΛ _ (hzy _ hs).1 (hzy _ hs).2
    have ht := hfR _ (hzy _ hs).1 (hzy _ hs).2
    have hsum := add_mem h1 h2'
    have heq : y + z - f (y + z) + (f (y + z) + -y - f (f (y + z) + -y)) = z - f (f (y + z) + -y) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ ht hsum).symm
  · have ht := hfR _ (hzy z hz).1 (hzy z hz).2
    have h1 := hfΛ _ (hzy z hz).1 (hzy z hz).2
    have h2' := hfΛ _ (hyz _ ht).1 (hyz _ ht).2
    have hs := hfR _ (hyz _ ht).1 (hyz _ ht).2
    have hsum := add_mem h1 h2'
    have heq : z + -y - f (z + -y) + (y + f (z + -y) - f (y + f (z + -y))) = z - f (y + f (z + -y)) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ hs hsum).symm

end GlobalTheory.CosetEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_avg_has_type : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @GlobalTheory.KFinCuspAvgType.isTypeAt_avgN | exact GlobalTheory.KFinCuspAvgType.isTypeAt_avgN | (intros; apply GlobalTheory.KFinCuspAvgType.isTypeAt_avgN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgIsCuspStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_avg_is_cusp : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ → IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @GlobalTheory.KFinCuspApprox.isCuspFun_avgN | exact GlobalTheory.KFinCuspApprox.isCuspFun_avgN | (intros; apply GlobalTheory.KFinCuspApprox.isCuspFun_avgN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory

theorem isIsotypic_of_uEquiv_left {G X Y K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {δ : G →* (X →L[ℂ] X)} {δ' : G →* (Y →L[ℂ] Y)} {ρ : G →* (K →L[ℂ] K)}
    (e : ∃ A : X ≃ₗᵢ[ℂ] Y, ∀ g x, A (δ g x) = δ' g (A x)) (h : IsIsotypic δ ρ) : IsIsotypic δ' ρ := by
  obtain ⟨A, hA⟩ := e
  refine eq_top_iff.2 (h.ge.trans (isoPart_le (Submodule.isClosed_topologicalClosure _) fun T hT x => ?_))
  have hs : ∀ g y, A.symm (δ' g y) = δ g (A.symm y) := fun g y => by
    apply A.injective
    rw [hA g, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hx : T x = (T ∘L (A.symm : Y →L[ℂ] X)) (A x) := by simp
  rw [hx]
  refine apply_mem_isoPart (mem_homIn_top.2 fun g y => ?_) _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hs]
  exact (mem_homIn_top.1 hT) g _

theorem hasDSComp_of_trace_ne_zero : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  obtain ⟨δ, hδ⟩ := hFl.exists_hasCompPl (isCMExt_host D) (isHermND_gram (V := V)) hπ (.inl (placeOf D τ))
  have hδ' : IsIsotypic (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) δ.π
      (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ
  obtain ⟨c', hc', himp⟩ := GlobalTheory.T.discrete_series_test_function_trace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
    have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
    have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
    obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
    haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
    have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) :=
      (continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem _)).integrable_of_hasCompactSupport (hmem _).1
    have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
      isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
    have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
    let δw : GArch D.sp.cm.sig V.gram (placeOf D τ) →* (δ.H →L[ℂ] δ.H) := δ.π
    have hδirr : IsIrrUnitary δw := δ.isIrr
    have hδw : IsIsotypic δw (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ'
    have hc'w : HasTrace (repOp δw (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δw _ hδirr hπw hδw Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  first | exact @GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | exact GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | (intros; apply GlobalTheory.LeviNormInj.eq_of_phase_integral_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  first | exact @GlobalTheory.IsoMean.integrable_coef | exact GlobalTheory.IsoMean.integrable_coef | (intros; apply GlobalTheory.IsoMean.integrable_coef <;> assumption)
end

