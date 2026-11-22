import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0908
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LanglandsMultisegmentsOfSeg
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0909
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JTilShiftBlock
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory

theorem jTil_shift_block : ∀ (l n t : ℕ) (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n t h w η typ U → ∀ (a : ZMod n) (S : Set ℚ), (∀ b : ℤ, ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ S) ∧ (U a).count (b + w a) ≤ 1) → ∀ b : ℤ, (if ((b : ℚ) ∈ S ∨ ∃ c : ℕ, c < t ∧ (b : ℚ) = c) then (1 : ℤ) else 0) = tableLineDegreeTwo.jTil U w t a (b + w a) := by
  intro l n t h w η typ U hS a S hU b
  have hsg : 0 ≤ tableLineDegreeTwo.sg n l h a := by
    unfold tableLineDegreeTwo.sg Formalism.WachCohomologyFacts.V2.sgN
    exact Int.floor_nonneg.mpr (tsum_nonneg fun j => by positivity)
  obtain ⟨_, _, _, hG, hB, _, hT2, _⟩ := hS a
  have hblk : (∃ c : ℕ, c < t ∧ (b : ℚ) = c) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor
    · rintro ⟨c, hc, hbc⟩
      have : b = (c : ℤ) := by exact_mod_cast hbc
      omega
    · rintro ⟨h0, h1⟩
      refine ⟨b.toNat, by omega, ?_⟩
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hwin : ((w a : ℤ) ≤ b + w a ∧ b + w a ≤ (w a : ℤ) + t - 1) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> omega
  have hc1 := (hU b).2
  have hcS : (b : ℚ) ∈ S → (U a).count (b + w a) = 1 := (hU b).1.2
  have hcN : (b : ℚ) ∉ S → (U a).count (b + w a) = 0 := fun hn => by
    have := mt (hU b).1.1 hn
    omega
  have hboth : (b : ℚ) ∈ S → ¬ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    rintro hbS ⟨h0, h1⟩
    have hmem : b + (w a : ℤ) ∈ U a := Multiset.count_pos.mp (by rw [hcS hbS]; omega)
    have hlow : b + (w a : ℤ) ∈ tableLineDegreeTwo.lows (typ a) (h a) (η a) (U a) := by
      unfold tableLineDegreeTwo.lows
      rw [Multiset.mem_filter]
      refine ⟨hmem, ?_⟩
      unfold Formalism.WachCohomologyFacts.V2.InWinN
      cases hty : typ a
      · have := hB hty
        simp only [Bool.false_eq_true, if_false]
        constructor <;> omega
      · have := hG hty
        simp only [if_true]
        constructor <;> omega
    have hy : b + (w a : ℤ) ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (w a) t := by
      unfold Formalism.WachCohomologyFacts.Top.GlobalTheory
      rw [Finset.mem_Icc]
      constructor <;> omega
    have := hT2 _ hlow _ hy
    rw [sub_self, abs_zero] at this
    linarith
  unfold tableLineDegreeTwo.jTil
  by_cases hbS : (b : ℚ) ∈ S
  · have hn := hboth hbS
    rw [if_pos (Or.inl hbS), if_neg (by rwa [hwin]), hcS hbS]
    simp
  · rw [hcN hbS]
    by_cases hbl : 0 ≤ b ∧ b ≤ (t : ℤ) - 1
    · rw [if_pos (Or.inr (hblk.2 hbl)), if_pos (hwin.2 hbl)]
      simp
    · rw [if_neg (by rintro (h1 | h1); exact hbS h1; exact hbl (hblk.1 h1)), if_neg (by rwa [hwin])]
      simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionOfEigenCentralSeriesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_condition_of_eigen_central_series : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D → SumRepresentations.Conclusion41 D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  first | exact @GlobalTheory.PassOp.main | exact GlobalTheory.PassOp.main | (intros; apply GlobalTheory.PassOp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLargeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_bound_family_large : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x), GlobalTheory.NFacts.Facts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  first | exact @GlobalTheory.LargeJumps.jump_bound_of_facts_large_family | exact GlobalTheory.LargeJumps.jump_bound_of_facts_large_family | (intros; apply GlobalTheory.LargeJumps.jump_bound_of_facts_large_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExhaustionGLHolds
section
theorem GlobalTheory.langlandsExhaustionGL_holds : GlobalTheory.Published.LanglandsExhaustionGL :=
  CompanionTheory.Exh.langlandsExhaustionGL_of_seg CompanionTheory.RgGu.segmentRepresentation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsMultisegmentsOutright
section
namespace GlobalTheory

theorem langlandsMultisegments_outright : GlobalTheory.Published.LanglandsMultisegments :=
  CompanionTheory.Exh.langlandsMultisegments_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExponeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  first | exact @GlobalTheory.LengthH0Bound.main | exact GlobalTheory.LengthH0Bound.main | (intros; apply GlobalTheory.LengthH0Bound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverComp

theorem forms_mul_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  intro D T hL j hj σ hσ C hU N hN hMN hW w hw1 hw2 hw3 a n
  obtain ⟨hlev, hA, hinc, hUnf, hdom, hr, g, e, F, ik, φ, th, hmod, hth, hdict⟩ := hU
  have hpq := (GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨hio, -⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj σ hσ (T.V j σ) rfl hr
  have hgood : GoodEmb C.d.c₂ C.σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  have hMN' : C.d.l₂.M' ∣ N := by
    simpa [Level.M', hA] using hMN
  have key := GlobalTheory.T.coverSections_mul_stable_weberValues D T.Q hL.pins j hj C.d.l₂ C.d.Xo₂ C.d.c₂ C.σ₂ (T.V j σ) D.R.r hr C.U₂ C.dict₂
    (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) g e F ik φ th (T.x₀ j σ) hio hpos hA hgood hmod hdict hdom
    hUnf N hN hMN' hW w hw1 hw2 hw3 a n
  have hrd : ∀ f f' : Rul C.d.Xo₂ C.d.c₂,
      (∀ h, rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2 = C.σ₂ (w h) * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2) →
      C.rd a f' = fun h => C.σ₂ (w h) * C.rd a f h := by
    intro f f' hff
    funext h
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul]
    change _ * (_ * rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2) = _ * (_ * (_ * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2))
    rw [hff h]
    ring
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, ⟨hf, hc⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, -⟩ := key f hf
    exact ⟨f', ⟨hf', h2 _ hc⟩, hrd f f' h1⟩
  · rintro S hS _ ⟨f, ⟨⟨hf, hc⟩, hv⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, h3⟩ := key f hf
    exact ⟨f', ⟨⟨hf', h2 _ hc⟩, fun la hla v hvv => h3 la (hS la hla) (hv la hla) v hvv⟩, hrd f f' h1⟩

end GlobalTheory.CoverComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.EisAbsPf

abbrev LA : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M)

abbrev LB : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ

theorem lintegral_ne_top_of_bounds {X : Type*} [MeasurableSpace X] [Mul X] (ν : Measure X) (𝓖 : Set X)
    (hfin : ν 𝓖 < ⊤) (Γ : Set X) (h q : X → ℝ) (hq : ∀ g, 0 ≤ q g)
    (htr : ∀ g, ∃ γ ∈ Γ, h (γ * g) ≤ 2 * q g) (hh : ∀ g, 0 ≤ h g)
    (S : X → X → ENNReal) (hinv : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, ∀ g₁ g₂, S (γ₁ * g₁) (γ₂ * g₂) = S g₁ g₂)
    (M : ℕ) (C : ℝ) (hC : ∀ g₁ g₂, S g₁ g₂ ≤ ENNReal.ofReal (C * (h g₁ * h g₂) ^ M))
    (a b : X → ℂ) (C₁ C₂ : ℝ) (hC₁ : ∀ g, ‖a g‖ * q g ^ M ≤ C₁) (hC₂ : ∀ g, ‖b g‖ * q g ^ M ≤ C₂) :
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ := by
  have hpt : ∀ g₁ g₂, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
    intro g₁ g₂
    obtain ⟨γ₁, hγ₁, e1⟩ := htr g₁
    obtain ⟨γ₂, hγ₂, e2⟩ := htr g₂
    have hq₁ := hq g₁
    have hq₂ := hq g₂
    have hS1 : S g₁ g₂ ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) := by
      rw [← hinv γ₁ hγ₁ γ₂ hγ₂ g₁ g₂]
      refine (hC _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hh' : h (γ₁ * g₁) * h (γ₂ * g₂) ≤ (2 * q g₁) * (2 * q g₂) :=
        mul_le_mul e1 e2 (hh _) (by linarith)
      calc C * (h (γ₁ * g₁) * h (γ₂ * g₂)) ^ M
          ≤ |C| * ((2 * q g₁) * (2 * q g₂)) ^ M :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg (hh _) (hh _)) hh' M) (pow_nonneg (mul_nonneg (hh _) (hh _)) M)
              (abs_nonneg _)
        _ = |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := by
            rw [show (2 * q g₁) * (2 * q g₂) = 4 * (q g₁ * q g₂) by ring, mul_pow, mul_pow]; ring
    have hn1 : ‖a g₁‖ₑ = ENNReal.ofReal ‖a g₁‖ := (ofReal_norm_eq_enorm _).symm
    have hn2 : ‖b g₂‖ₑ = ENNReal.ofReal ‖b g₂‖ := (ofReal_norm_eq_enorm _).symm
    have a1 := hC₁ g₁
    have a2 := hC₂ g₂
    have p1 : 0 ≤ ‖a g₁‖ * q g₁ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₁ M)
    have p2 : 0 ≤ ‖b g₂‖ * q g₂ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₂ M)
    have c0 : 0 ≤ |C| * 4 ^ M := by positivity
    calc S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ
        ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) * ENNReal.ofReal ‖a g₁‖ * ENNReal.ofReal ‖b g₂‖ := by
          rw [hn1, hn2]; gcongr
      _ = ENNReal.ofReal (|C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)) := by
          have c1 : 0 ≤ |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := mul_nonneg c0 (mul_nonneg (pow_nonneg hq₁ M) (pow_nonneg hq₂ M))
          rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_mul (mul_nonneg c1 (norm_nonneg _))]
          congr 1; ring
      _ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc |C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)
              ≤ |C| * 4 ^ M * C₁ * (‖b g₂‖ * q g₂ ^ M) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 c0) p2
            _ ≤ |C| * 4 ^ M * C₁ * C₂ :=
                mul_le_mul_of_nonneg_left a2 (mul_nonneg c0 (p1.trans a1))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖) ?_ ?_
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hfin.ne
  · calc ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν
        ≤ ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) ∂ν ∂ν :=
          lintegral_mono fun g₁ => lintegral_mono fun g₂ => hpt g₁ g₂
      _ = ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖 := by
          rw [setLIntegral_const, setLIntegral_const]

theorem eisAbs_of_bounds (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hA : LA) (hB : LB) :
    ∀ D : D7, EisAbs D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2
  obtain ⟨M, C, hC⟩ := hA D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2
  have e : ∀ γ g : GA D W, om (1, γ * g) = om (1, γ) * om (1, g) := by
    intro γ g; rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hinv : ∀ γ₁ ∈ (GQ W : Set (GA D W)), ∀ γ₂ ∈ (GQ W : Set (GA D W)), ∀ g₁ g₂ : GA D W,
      (∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁ * g₁) f₁) (om (1, γ₂ * g₂) f₂)‖ₑ) =
        ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ := by
    intro γ₁ hγ₁ γ₂ hγ₂ g₁ g₂
    rw [e γ₁ g₁, e γ₂ g₂, Module.End.mul_apply, Module.End.mul_apply]
    exact hB D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ (hS.weil.om_pres _ _ h1) (hS.weil.om_pres _ _ h2)
      γ₁ hγ₁ γ₂ hγ₂
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA1 hC1 M
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA2 hC2 M
  have hfin : νW 𝓖 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV W νW 𝓖 hS.haarW hS.fdW
  have key := lintegral_ne_top_of_bounds νW 𝓖 hfin (GQ W : Set (GA D W))
    (fun g => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g : ℝ)) (fun g => (GlobalTheory.CuspDecay.quotHeight θ W g : ℝ))
    (fun g => NNReal.coe_nonneg _)
    (fun g => by
      obtain ⟨γ, hγ, hle⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
      exact ⟨γ, hγ, by exact_mod_cast hle⟩)
    (fun g => NNReal.coe_nonneg _)
    (fun g₁ g₂ => ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ) hinv M C hC φ₁ φ₂ C₁ C₂ hC₁ hC₂
  refine ne_top_of_le_ne_top key (le_of_eq ?_)
  refine lintegral_congr fun g₁ => lintegral_congr fun g₂ => ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

theorem eisAbs : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, EisAbs D :=
  fun hP => eisAbs_of_bounds hP GlobalTheory.Mem.VolFin.finVol GlobalTheory.T.siegelWeilLagrangianTerms_abs_tsum_le_heightPoly GlobalTheory.T.siegelWeil_tsum_enorm_rational_invariant

end GlobalTheory.EisAbsPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSelfCuspRapidSpanNeTopStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_self_cusp_rapid_span_ne_top : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a) (ω : HChar E),
    ω.IsUnitary → π.HasCentChar ω → ∀ F : GA E a → ℂ, F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ, 1 < x →
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ := by
  first | exact @GlobalTheory.RSThetaSelf.lintegral_ne_top | exact GlobalTheory.RSThetaSelf.lintegral_ne_top | (intros; apply GlobalTheory.RSThetaSelf.lintegral_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModulesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBlochKatoCondition_of_wachModules : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → WAll D HW F → CrysOnCond D HW F → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  first | exact @GlobalTheory.TBLocal.main | exact GlobalTheory.TBLocal.main | (intros; apply GlobalTheory.TBLocal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundZeroAtLargePrimesOfCongruenceBoundStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  first | exact @GlobalTheory.NLink.RowE.main | exact GlobalTheory.NLink.RowE.main | (intros; apply GlobalTheory.NLink.RowE.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOfLocalTheoremHypW
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.TBLocalW

theorem tb_of_localW : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ),
    LocalSituation.Conclusion4 D HW F →
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) →
    TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  intro D HW F i r π M0 h0 cB hP hW hF hJ
  obtain ⟨hl2, hJw⟩ := hJ
  intro w hw C hG
  obtain ⟨hIn, hKs, hJC⟩ := hJw w hw
  have hs : Good (D.nbr i w hw).Kw 1 C.LL := hG.good_one hl2 hKs
  have hP1 := hP (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs
  have hTB := hP1.1
  have hTBe := hP1.2
  have hWs := hW w hw C hs
  have hFa := hF w hw C
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let Yt : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let Y := kerY Yt p e₀ hpe hp hint he₀
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hcjY := cj_sub hFa (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
    have hJY := hJC C hs Y hcjY.1 hcjY.2
    have hWY := hWs Y M0 h0 hcjY.1 hJY.1
    have hJYt := hJC C hs Yt hcrys hjmp
    have hCt := (hWs Yt M0 h0 hcrys hJYt.1).1
    haveI : IsTopologicalRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).LL :=
      inferInstanceAs (IsTopologicalRing ↥C.LL.1)
    haveI : IsDomain (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsDomain ↥(OL C.LL))
    haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsPrincipalIdealRing ↥(OL C.LL))
    exact GlobalTheory.TBLocal.tb_part1 (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
      Yt p e₀ hpe hp hint he₀ Subtype.val_injective _ hTB e M0 h0 cB VeL hE.1 hE.2 hCt hWY (hJY.2 e he) φ hφ
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hTBe e VeL hE.1 hE.2
    exact GlobalTheory.TBLocal.tbe_clauses (Br.PD D.loc D.nbr i w hw) Le _ _ hIn e cB hT.2.1 hT.2.2 (hT.1 cB)

end GlobalTheory.TBLocalW
end
end

