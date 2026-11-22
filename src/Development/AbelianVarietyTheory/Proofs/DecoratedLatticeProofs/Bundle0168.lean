import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.LStab
section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem col_mem_hatL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ)
    (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  rw [hβ]
  intro k
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem exists_fg_sub {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) :
    ∃ Λ₁ ≤ Λ, Λ₁.FG ∧ Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ := by
  classical
  have hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧
      β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j =>
    Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)
  choose T hT hmem using hcol
  let U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := Finset.univ.biUnion T
  have hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨x, hx, e⟩ := hT j hj
    exact ⟨x, hx, e⟩
  choose! pre hpre hpref using hUsub
  have hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hpre y hy
  refine ⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle,
    Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  · have hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by
      intro j
      refine Submodule.span_mono ?_ (hmem j)
      intro y hy
      have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩
      exact ⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩
    intro y hy
    have hc := (hβ y).1 hy
    obtain ⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1) := by
      have e1 : y = β.1 *ᵥ c := by
        rw [hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      conv_lhs => rw [e2]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
    rw [ey]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)

theorem latLoc_eq {Λ₁ Λ : Submodule (𝓞 E) (Fin n → E)} (hle : Λ₁ ≤ Λ) (hfg : Λ₁.FG)
    (heq : Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.latLoc F Λ₁ v = GlobalTheory.AdelicU.latLoc F Λ v := by
  apply le_antisymm
  · intro y hy
    exact GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
  · intro y hy
    refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ :=
      heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E)) :=
      (GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v
    have h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i := by
      funext i
      simp [GlobalTheory.AdelicU.vecLoc]
    rw [h4] at h3
    have h5 := (GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem
      ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3
    convert h5 using 1
    funext i
    show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

end General

section Adelic
variable {D : D7}

theorem finE_mem_St_iff_of_fg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (hfg : Λ.FG) (g : GA D V) :
    Lev.finE V g ∈ Formalism.L2.DIV.St β ↔
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  have h1 := GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)
  have h3 := GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g
  have h4 := GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

end Adelic

theorem finE_mem_St_iff_stabLoc : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  intro D V β Λ hfr g
  obtain ⟨Λ₁, hle, hfg, heq⟩ := exists_fg_sub hfr
  have hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁ := fun x => by
    rw [heq]; exact hfr x
  rw [finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]
  have hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := fun v => by
    unfold GlobalTheory.AdelicU.stabLoc
    rw [latLoc_eq hle hfg heq v]
  simp only [hL]

end GlobalTheory.ChainOnto.LStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepRule

theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

theorem rulePar_step : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X →
    ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧
      RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  intro D X h3 h4 h5 k hk τ
  obtain ⟨al, be, ga, de, hd, hfar, e0, e1⟩ := hk τ
  have hT : ThetaPar D.R.t (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) (expT D k τ) (expS D k τ) :=
    ⟨al, be, ga, de, e0, Or.inl ⟨hd, e1⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom (expT D k τ) (((D.R.t : ℚ) + 3) / 2) (parA (Ptw D) k τ) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    rw [e0] at hs
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + expT D k τ := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩,
    rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inr hT⟩⟩

end GlobalTheory.StepRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceComm

open GlobalTheory.OrientedHeis (theta_add theta_smul theta_dRho)

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_comm {B : (X → ℂ) → (X → ℂ)} (hA : ∀ i f, P f → P (A i f))
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    B (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A i g) (B f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [hBA _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l), ih]

theorem pure_comm {B : (X → ℂ) → (X → ℂ)} (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Badd : ∀ f f', P f → P f' → B (f + f') = B f + B f') (Bsm : ∀ (a : ℂ) f, P f → B (a • f) = a • B f)
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    B (pureTensorL A f Q) = pureTensorL A (B f) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [Bsm _ _ (GlobalTheory.FockIndep.foldr_mem hA hf _), foldr_comm hA hBA hf]
  | add p q hp hq =>
    rw [map_add, map_add, Badd _ _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _) (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _),
      hp, hq]

theorem pure_fun_add (hA : ∀ i f, P f → P (A i f)) (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f') {f f' : X → ℂ} (hf : P f) (hf' : P f')
    (Q : MvPolynomial ι ℂ) : pureTensorL A (f + f') Q = pureTensorL A f Q + pureTensorL A f' Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (f + f') =
      l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Aadd _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_add]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
    abel

theorem pure_fun_smul (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (a : ℂ) {f : X → ℂ} (hf : P f)
    (Q : MvPolynomial ι ℂ) : pureTensorL A (a • f) Q = a • pureTensorL A f Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (a • f) = a • l.foldr (fun i g => A i g) f := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Asm _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_comm]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, smul_add]

end Generic

section Places

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ ≠ τ')
include hψ hθ hne

theorem dRho_comm_ne (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) =
      Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) := by
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' z' hf]
  simp [GlobalTheory.FockIndep.omDir, hne]

theorem dRho_aPlus_ne (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (aPlus (heisO ψ S T) θ τ' J u f) =
      aPlus (heisO ψ S T) θ τ' J u (Datum.dRho (heisO ψ S T) θ τ z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq,
    GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    GlobalTheory.FockIndep.dRho_add hψ hθ _ _ (ht _ _) (theta_smul _ (ht _ _)), GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (ht _ _),
    dRho_comm_ne hψ hθ hne _ _ hf, dRho_comm_ne hψ hθ hne _ _ hf]

theorem aPlus_comm_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (aPlus (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq τ J z (aPlus (heisO ψ S T) θ τ' J' u f), dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    dRho_aPlus_ne hψ hθ hne _ _ _ hf, ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))), ← GlobalTheory.FockIndep.aPlus_eq]

theorem annih_aPlus_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (annih (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [annih, annih, dRho_aPlus_ne hψ hθ hne _ _ _ hf, dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _))]

end Places

section Weil

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hW : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
  {τ τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'))
include hW hθ hne hg

theorem om_dRho_fix (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (Datum.dRho (heisO ψ V W) θ τ z f) =
      Datum.dRho (heisO ψ V W) θ τ z (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hW hθ _ _ τ z hf]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V (atTau θ V τ' g)) = 1 :=
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hg).2.2 τ hne
  have h3 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ (atTau θ V τ' g)
  rw [h2, Matrix.one_mul] at h3
  rw [h1, h3, Matrix.one_mul, Matrix.mul_one]

theorem om_aPlus_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (aPlus (heisO ψ V W) θ τ J u f) = aPlus (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq, map_smul, map_add, map_smul, om_dRho_fix hW hθ hne hg _ hf,
    om_dRho_fix hW hθ hne hg _ hf]

theorem om_annih_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (annih (heisO ψ V W) θ τ J u f) = annih (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [annih, annih, map_add, map_smul, om_dRho_fix hW hθ hne hg _ hf, om_dRho_fix hW hθ hne hg _ hf]

end Weil

theorem twoPlace_comm : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hW τ τ' hne F hF
  dsimp only
  have hψ := hW.std
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ ρ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g) :=
    fun ρ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ ρ _ _ h
  have Aadd : ∀ ρ (k : Fin W.rank × Fin V.rank) g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (g + g') =
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g +
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g' :=
    fun ρ _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ ρ _ _ h h'
  have Asm : ∀ ρ (k : Fin W.rank × Fin V.rank) (a : ℂ) g, IsThetaFunO ψ V W g →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (a • g) =
      a • aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g :=
    fun ρ _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ ρ _ _ a h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt
  refine ⟨fun P => GlobalTheory.FockIndep.pure_mem hadd hsm (hA τ') hF P, fun P hv z => ?_, fun P Q => ?_, fun g hg => ⟨?_, ?_⟩⟩
  · rw [pure_comm hadd hsm (hA τ') (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ τ _ z h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z a h)
      (fun k g hg => annih_aPlus_ne hψ hθ hne _ _ _ _ hg) hF P, hv z]
    have h0 := pure_fun_smul (hA τ') (Asm τ') 0 hF P
    rwa [zero_smul, zero_smul] at h0
  · symm
    refine pure_comm (B := fun g => pureTensorL (fun k : Fin W.rank × Fin V.rank =>
        aPlus (heisO ψ V W) θ τ' (cplxO (cart M τ') (cart M' τ')) (unitMap (onb M τ') (onb M' τ') k.1 k.2)) g Q)
      hadd hsm (hA τ) (fun _ _ h h' => pure_fun_add (hA τ') hadd hsm (Aadd τ') h h' Q)
      (fun a _ h => pure_fun_smul (hA τ') (Asm τ') a h Q) (fun k g hg => ?_) hF P
    exact (pure_comm hadd hsm (hA τ') (Aadd τ k) (Asm τ k)
      (fun j h hh => aPlus_comm_ne hψ hθ hne _ _ _ _ hh) hg Q).symm
  · intro hv z
    rw [← om_annih_fix hW hθ hne hg _ _ hF, hv z, map_zero]
  · intro P
    exact pure_comm hadd hsm (hA τ) (fun f f' _ _ => map_add _ f f') (fun a f _ => map_smul _ a f)
      (fun k h hh => om_aPlus_fix hW hθ hne hg _ _ hh) hF P

end GlobalTheory.TwoPlaceComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  first | exact @GlobalTheory.Unf.FB.basePoint_spec | exact GlobalTheory.Unf.FB.basePoint_spec | (intros; apply GlobalTheory.Unf.FB.basePoint_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FrameAct

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  simp

theorem finE_inv_val' {D : D7} (V : HSp D) (g : GA D V) :
    ((Lev.finE V g)⁻¹).1 = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val' {D : D7} {n : ℕ} (β y : GL (Fin n) (Lev.EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (Lev.EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem frMapO_actO_left : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]

end GlobalTheory.ChainOnto.FrameAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
section
open Formalism.BasicNotions

namespace GlobalTheory.Core.Rk.GapOfNodes

theorem harishChandraNodesFarApart_of_cubic_node_gap : ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  intro D H
  have hN : D.R.N D.R.m = D.R.rankX' + 1 := factXm D.R
  refine ⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩
  have h := H D.u₀ τ i.1 hi
  rw [D.hcW_b D.u₀ τ] at h
  simp only [Fin.eta] at h
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
  have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  exact_mod_cast key

end GlobalTheory.Core.Rk.GapOfNodes
end

