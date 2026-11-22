import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GlobProj

theorem weak_integral_prod {X Y H : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (R : X × Y → (H →L[ℂ] H)) (A : X → (H →L[ℂ] H)) (B : Y → (H →L[ℂ] H))
    (hR : ∀ g k, R (g, k) = A g * B k) (hn : ∀ z v, ‖R z v‖ = ‖v‖)
    (a : X → ℂ) (e : Y → ℂ) (ha : Integrable a μ) (he : Integrable e ν) (P E : H →L[ℂ] H)
    (hP : ∀ x y : H, ⟪x, P y⟫_ℂ = ∫ g, a g * ⟪x, A g y⟫_ℂ ∂μ)
    (hE : ∀ x y : H, ⟪x, E y⟫_ℂ = ∫ k, e k * ⟪x, B k y⟫_ℂ ∂ν) (x y : H)
    (hm : AEStronglyMeasurable (fun z => ⟪x, R z y⟫_ℂ) (μ.prod ν)) :
    ⟪x, (P.comp E) y⟫_ℂ = ∫ z, (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ ∂(μ.prod ν) := by
  have hbd : ∀ z, ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun z => by
    calc ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖R z y‖ := norm_inner_le_norm x _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hae : Integrable (fun z : X × Y => a z.1 * e z.2) (μ.prod ν) := ha.mul_prod he
  have hint : Integrable (fun z : X × Y => (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ) (μ.prod ν) := by
    refine Integrable.mono' (hae.norm.mul_const (‖x‖ * ‖y‖)) (hae.aestronglyMeasurable.mul hm) ?_
    refine ae_of_all _ fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd z) (norm_nonneg _)
  rw [integral_prod _ hint, ContinuousLinearMap.comp_apply, hP]
  congr 1
  funext g
  dsimp only
  have h1 : ⟪x, A g (E y)⟫_ℂ = ∫ k, e k * ⟪x, R (g, k) y⟫_ℂ ∂ν := by
    rw [← ContinuousLinearMap.adjoint_inner_left (A g) (E y) x, hE]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, hR, ContinuousLinearMap.mul_apply]
  rw [h1, ← integral_const_mul]
  congr 1
  funext k
  ring

theorem conv_prod (B : RowsAut) (a : B.I.Ginf → ℂ) (P : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (ha : Integrable a (muInf B.I)) (hP : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) a P) :
    B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) (P.comp B.Re) ∧
      ∀ T, B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) T → T = P.comp B.Re := by
  obtain ⟨-, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : SFinite (muInf B.I) := by unfold muInf; infer_instance
  have hE := B.Re_spec
  have key : ∀ x y : B.I.L2 B.μf B.fund, ⟪x, (P.comp B.Re) y⟫_ℂ =
      ∫ g, (fun z : B.I.GA => a z.1 * B.e z.2) g * ⟪x, B.R g y⟫_ℂ ∂(B.I.muA B.μf) := by
    intro x y
    have hm : AEStronglyMeasurable (fun z => ⟪x, B.R z y⟫_ℂ) ((muInf B.I).prod B.μf) :=
      (continuous_const.inner (hcont y)).aestronglyMeasurable
    exact weak_integral_prod (muInf B.I) B.μf B.R (fun g => B.R (g, 1)) (fun k => B.R (1, k))
      (fun g k => by rw [← hmul, Prod.mk_mul_mk, mul_one, one_mul]) (fun z v => hnorm z v)
      a B.e ha hE.1 P B.Re hP.2 hE.2 x y hm
  have hint : Integrable (fun z : B.I.GA => a z.1 * B.e z.2) (B.I.muA B.μf) := ha.mul_prod hE.1
  refine ⟨⟨hint, key⟩, fun T hT => ?_⟩
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [hT.2, key]

theorem comm_of_isOpOf {G L : Type} [MeasurableSpace G] [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    {μ : Measure G} {π : G → (L →L[ℂ] L)} {φ : G → ℂ} {P E : L →L[ℂ] L} (hP : IsOpOf μ π φ P)
    (hE : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ) (hc : ∀ g, E.comp (π g) = (π g).comp E) (y : L) :
    P (E y) = E (P y) := by
  refine ext_inner_left ℂ fun x => ?_
  rw [hP.2 x (E y), ← hE x (P y), hP.2 (E x) y]
  congr 1
  funext g
  congr 1
  have h := congrArg (fun T : L →L[ℂ] L => T y) (hc g)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h, hE]

theorem abstract_count {G H L : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (σ : G → (H →L[ℂ] H)) (π : G → (L →L[ℂ] L)) (w : H)
    (hw : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H))
    (P E : L →L[ℂ] L) (hPP : ∀ y, P (P y) = P y) (hPs : ∀ x y : L, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ)
    (hEE : ∀ y, E (E y) = E y) (hEs : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ)
    (hPE : ∀ y, P (E y) = E (P y)) (hc : ∀ g, E.comp (π g) = (π g).comp E)
    (hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : H →L[ℂ] L, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w)
    (S : Submodule ℂ (H →L[ℂ] L))
    (hS : ∀ A, A ∈ S ↔ ∃ A₀ : H →L[ℂ] L, (∀ g : G, A₀ ∘L σ g = π g ∘L A₀) ∧ E ∘L A₀ = A) :
    IsOrthProjOnto (P.comp E) (LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) ∧
      (∀ A ∈ S, (P.comp E) (A w) = A w) ∧
      (∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y) ∧
      Nonempty (S ≃ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) := by
  have hQQ : ∀ y, P (E (P (E y))) = P (E y) := fun y => by rw [← hPE, hPP, hEE]
  have hSi : ∀ A ∈ S, ∀ g, A ∘L σ g = π g ∘L A := by
    intro A hA g
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    rw [ContinuousLinearMap.comp_assoc, hA₀ g, ← ContinuousLinearMap.comp_assoc, hc g,
      ContinuousLinearMap.comp_assoc]
  have huniq : ∀ A ∈ S, ∀ A' ∈ S, A w = A' w → A = A' := by
    intro A hA A' hA' h
    refine ContinuousLinearMap.ext_on hw ?_
    rintro _ ⟨g, rfl⟩
    have e1 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A hA g)
    have e2 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A' hA' g)
    simp only [ContinuousLinearMap.comp_apply] at e1 e2
    show A (σ g w) = A' (σ g w)
    rw [e1, e2, h]
  have hfix : ∀ A ∈ S, (P.comp E) (A w) = A w := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    obtain ⟨y, hy⟩ := (hr (A₀ w)).2 ⟨A₀, hA₀, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [hEE, hPE, ← hy, hPP]
  have hex : ∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y := by
    intro y hy
    simp only [ContinuousLinearMap.comp_apply] at hy
    obtain ⟨io, hio, hyw⟩ := (hr y).1 ⟨E y, hy⟩
    have hEy : E y = y := by rw [← hy, ← hPE, hEE]
    have hmem : E ∘L io ∈ S := (hS _).2 ⟨io, hio, rfl⟩
    have hval : (E ∘L io) w = y := by rw [ContinuousLinearMap.comp_apply, ← hyw, hEy]
    refine ⟨E ∘L io, ⟨hmem, hval⟩, ?_⟩
    rintro A ⟨hA, hAw⟩
    exact huniq A hA _ hmem (by rw [hAw, hval])
  refine ⟨⟨?_, ?_, rfl⟩, hfix, hex, ?_⟩
  · ext y
    simp only [ContinuousLinearMap.comp_apply]
    exact hQQ y
  · intro x y
    simp only [ContinuousLinearMap.comp_apply]
    rw [hPs, hEs, ← hPE]
  · let f : S →ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L) :=
      { toFun := fun A => ⟨(A : H →L[ℂ] L) w, LinearMap.mem_range.2 ⟨(A : H →L[ℂ] L) w, hfix A A.2⟩⟩
        map_add' := fun A B => Subtype.ext rfl
        map_smul' := fun c A => Subtype.ext rfl }
    have hinj : Function.Injective f := fun A A' h =>
      Subtype.ext (huniq _ A.2 _ A'.2 (congrArg Subtype.val h))
    have hsurj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ (by
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
        exact hQQ z)
      exact ⟨⟨A, hA⟩, Subtype.ext hAw⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem globalProj_holds : GlobalProj := by
  intro B d hd hint
  obtain ⟨hReP, hReC, -⟩ := GlobalTheory.IdemProj.re_orth_proj B
  obtain ⟨hU, -, hF, hnw, hph⟩ := GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree B d hd
  obtain ⟨h1, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : (muInf B.I).IsHaarMeasure := by unfold muInf; infer_instance
  haveI : ∀ v, (muG (B.I.ε v)).IsMulRightInvariant := fun v =>
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ (B.I.ε v) g⟩
  haveI : (muInf B.I).IsMulRightInvariant := by unfold muInf; infer_instance
  let σh : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := hU.1, map_mul' := hU.2.1 }
  let πh : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) :=
    { toFun := fun g => B.R (g, 1), map_one' := h1
      map_mul' := fun a b => by rw [← hmul, Prod.mk_mul_mk, mul_one] }
  have hDne : ((∏ v, d v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
  have hsq : ∀ x y : B.Hs, Integrable (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) (muInf B.I) ∧
      ∫ g, ‖⟪y, σh g x⟫_ℂ‖ ^ 2 ∂(muInf B.I) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / (∏ v, d v) := by
    intro x y
    obtain ⟨hi, he⟩ := hF.2 x y x y
    have hre : ∀ g, RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) = ‖⟪y, σh g x⟫_ℂ‖ ^ 2 := by
      intro g
      rw [RCLike.star_def, RCLike.mul_conj]
      norm_cast
    have hfun : (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) =
        fun g => RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) := funext fun g => (hre g).symm
    rw [hfun]
    refine ⟨hi.re, ?_⟩
    rw [integral_re hi, he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have hc : ((‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v : ℝ) : ℂ) = (‖x‖ : ℂ) ^ 2 * (‖y‖ : ℂ) ^ 2 / ((∏ v, d v : ℝ) : ℂ) := by
      push_cast; ring
    rw [← RCLike.ofReal_re (K := ℂ) (‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v)]
    congr 1
    exact hc.symm
  have hintw : Integrable (fun g => ⟪B.tens B.w, σh g (B.tens B.w)⟫_ℂ) (muInf B.I) := by
    refine Integrable.mono' (hint.norm.const_mul (∏ v, d v)⁻¹)
      (continuous_const.inner (hU.2.2.2 (B.tens B.w))).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    show ‖⟪B.tens B.w, B.σs g (B.tens B.w)⟫_ℂ‖ ≤ (∏ v, d v)⁻¹ * ‖ph B d g‖
    rw [hph g, norm_mul, norm_star, Complex.norm_of_nonneg hF.1.le, ← mul_assoc,
      inv_mul_cancel₀ hF.1.ne', one_mul]
  obtain ⟨-, -, hPA⟩ := projAbs_holds B.I.Ginf (muInf B.I) B.Hs σh (fun g x => hU.2.2.1 g x) hU.2.2.2
    (∏ v, d v) hF.1 hsq (B.tens B.w) hnw hintw
  obtain ⟨⟨P, hP⟩, hPall⟩ := hPA (B.I.L2 B.μf B.fund) πh (fun g x => hnorm _ x)
    (fun x => (hcont x).comp (continuous_id.prodMk continuous_const))
  obtain ⟨hSP, -, -, hrange⟩ := hPall P hP
  have hphG : phG (∏ v, d v) σh (B.tens B.w) = ph B d := funext fun g => (hph g).symm
  have hPop : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) (ph B d) P := by
    refine ⟨by rw [← hphG]; exact hP.1, fun x y => ?_⟩
    rw [hP.2 x y, hphG]
    rfl
  have hPP : ∀ y, P (P y) = P y := fun y => by
    have h := congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hSP.isIdempotentElem.eq
    simpa using h
  have hPs : ∀ x y : B.I.L2 B.μf B.fund, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_left P y x, hSP.isSelfAdjoint.adjoint_eq]
  have hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : B.Hs →L[ℂ] B.I.L2 B.μf B.fund,
      (∀ g : B.I.Ginf, io ∘L B.σs g = B.R (g, 1) ∘L io) ∧ v = io (B.tens B.w) := fun v => by
    have h := Set.ext_iff.1 hrange v
    simp only [SetLike.mem_coe, LinearMap.mem_range, ContinuousLinearMap.coe_coe, Set.mem_setOf_eq] at h
    exact h
  have hS : ∀ A, A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re ↔
      ∃ A₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund, (∀ g : B.I.Ginf, A₀ ∘L B.σs g = B.R (g, 1) ∘L A₀) ∧
        B.Re ∘L A₀ = A := by
    intro A
    simp only [AutInst.eHom, Submodule.mem_map]
    constructor
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
  have hPE : ∀ y, P (B.Re y) = B.Re (P y) := comm_of_isOpOf hPop hReP.2.1 hReC
  have hEE : ∀ y, B.Re (B.Re y) = B.Re y := fun y =>
    congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hReP.1
  have hwd := hF.dense_span_orbit (B.tens B.w) (norm_ne_zero_iff.1 (by rw [hnw]; exact one_ne_zero))
  have hAC := abstract_count B.σs (fun g => B.R (g, 1)) (B.tens B.w) hwd P B.Re hPP hPs hEE hReP.2.1
    hPE hReC hr _ hS
  have hconv := conv_prod B (ph B d) P hint hPop
  refine ⟨hReP, hReC, ⟨P.comp B.Re, hconv.1⟩, fun T hT => ?_⟩
  obtain rfl := hconv.2 T hT
  obtain ⟨h1', h2', h3', ⟨eq⟩⟩ := hAC
  refine ⟨h1', h2', h3', fun hfd => ?_, (LinearEquiv.finrank_eq eq).symm⟩
  haveI := hfd
  exact LinearEquiv.finiteDimensional eq

end GlobalTheory.GlobProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengths
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MinorBound

open GlobalTheory.PlueckerBound GlobalTheory.Amp.GramFlag

theorem norm_det_inner_le_pow {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : ℕ} (u v : Fin l → E)
    (s t : Matrix (Fin l) (Fin l) ℂ) (hs : s.det = 1) (ht : t.det = 1) {R R' : ℝ}
    (hu : ∀ a, ‖∑ i, s i a • u i‖ ≤ R) (hv : ∀ a, ‖∑ i, t i a • v i‖ ≤ R') :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ R ^ l * R' ^ l := by
  have h := norm_det_inner_le (fun a => ∑ i, s i a • u i) (fun a => ∑ i, t i a • v i)
  rw [det_inner_sum_smul, ht, mul_one] at h
  have e : (Matrix.of fun a a' => ⟪∑ i, s i a • u i, v a'⟫_ℂ) = sᴴ * Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ := by
    ext a a'
    simp [Matrix.mul_apply, sum_inner, inner_smul_left, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, hs, star_one, one_mul] at h
  have h1 : ∀ {f : Fin l → E} {S : ℝ}, (∀ a, ‖f a‖ ≤ S) → ∏ a, ‖f a‖ ≤ S ^ l := fun {f S} hf => by
    have := Finset.prod_le_prod (s := Finset.univ) (fun a _ => norm_nonneg (f a)) (fun a _ => hf a)
    simpa using this
  have h0 : ∀ f : Fin l → E, 0 ≤ ∏ a, ‖f a‖ := fun f => Finset.prod_nonneg fun a _ => norm_nonneg _
  exact h.trans (mul_le_mul (h1 hu) (h1 hv) (h0 _) ((h0 _).trans (h1 hu)))

theorem exists_short (k r : ℕ) {l : ℕ} (hl : l ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r) :
    ∃ t : Matrix (Fin l) (Fin l) ℂ, t.det = 1 ∧
      ∀ a, eucl (∑ b, t b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b)))) ≤ Sg k r z x := by
  obtain ⟨u, hu, -⟩ := gramSchmidt_lengths k r z x hx
  refine ⟨(upper u).submatrix (Fin.castLE hl) (Fin.castLE hl), ?_, fun a => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · simp [upper]
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ a < b := not_lt.2 hab'.le
      simp [upper, h1, hab'.ne']
  · have e : ∑ b, (upper u).submatrix (Fin.castLE hl) (Fin.castLE hl) b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b))) =
        ∑ b, upper u b (Fin.castLE hl a) • (x⁻¹ *ᵥ bvec (eI k r b)) := by
      refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun b => rfl)
      intro b hb
      have hb' : l ≤ b.val := by
        by_contra h
        exact hb ⟨⟨b.val, by omega⟩, rfl⟩
      have ha := a.isLt
      have h1 : ¬ b < Fin.castLE hl a := by
        rw [Fin.lt_def, Fin.val_castLE]; omega
      have h2 : b ≠ Fin.castLE hl a := fun h => by
        rw [h, Fin.val_castLE] at hb'; omega
      simp [upper, h1, h2]
    rw [e, (hu _).1]
    exact (Finset.le_fold_max _).2 (Or.inr ⟨_, Finset.mem_univ _, le_rfl⟩)

theorem eucl_Hpk (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : eucl (Hpk k r *ᵥ v) = eucl v := by
  rw [eucl_eq, eucl_eq, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, (hpkFacts k r).1, (hpkFacts k r).2.1, Matrix.one_mulVec, dotProduct_comm]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem one_le_Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem norm_Dmin_le (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {γ x : Mat k r} (hγ : γ ∈ GG k r) (hx : x ∈ GG k r)
    (l : Fin (r + 1)) : ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ hH
  have hγx := hmul γ hγ x hx
  have hl : l.val ≤ r := Nat.le_of_lt_succ l.isLt
  obtain ⟨s, hs, hs'⟩ := exists_short k r hl z hγx
  obtain ⟨t, ht, ht'⟩ := exists_short k r hl z' hx
  have h := norm_det_inner_le_pow (E := EuclideanSpace ℂ (Fin (2 * r + k + 1)))
    (fun a => WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))
    (fun a => WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))) s t hs ht
    (R := Sg k r z (γ * x)) (R' := Sg k r z' x)
    (fun a => by
      have := hs' a
      rwa [eucl_eq, WithLp.toLp_sum] at this)
    (fun a => by
      have := ht' a
      rw [← eucl_Hpk, eucl_eq, Matrix.mulVec_sum, WithLp.toLp_sum] at this
      simpa only [Matrix.mulVec_smul, WithLp.toLp_smul] using this)
  have e : Dmin k r z z' γ l.castSucc = (Matrix.of fun a a' : Fin l.val =>
      ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))) : EuclideanSpace ℂ (Fin (2 * r + k + 1))),
        WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a'))))⟫_ℂ).det := by
    unfold Dmin
    congr 1
    ext a b
    have ha : a.val < r := lt_of_lt_of_le a.isLt hl
    have hb : b.val < r := lt_of_lt_of_le b.isLt hl
    rw [Matrix.of_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.submatrix_apply, Zhat,
      ← herm_mulVec (hinv _ hγx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (hinv _ hγ).1, Matrix.mul_one, fvec, fvec, dif_pos (by exact hb), dif_pos (by exact ha)]
    rfl
  rw [e]
  refine h.trans ?_
  rw [← mul_pow, mul_comm]
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_Sg ..) (one_le_Sg ..)) hl

theorem gramProj_le (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) :
    gramProj P (fun a : Fin j => x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) ≤ Sg k r z x ^ r := by
  obtain ⟨s, hs, hs'⟩ := exists_short k r hj z hx
  have h1 : ∀ a, ‖∑ i, s i a • P.starProjection (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj i))))‖ ≤
      Sg k r z x := fun a => by
    have := hs' a
    rw [eucl_eq, WithLp.toLp_sum] at this
    refine le_trans (le_of_eq ?_) ((P.norm_starProjection_apply_le _).trans this)
    simp only [map_sum, WithLp.toLp_smul, map_smul]
  have h := norm_det_inner_le_pow _ _ s s hs hs h1 h1
  have h0 := one_le_Sg k r z x
  refine le_trans ?_ (pow_le_pow_right₀ h0 hj)
  unfold gramProj
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [sq]
  exact h

theorem minor_gram_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  intro k r j hj z z' γ _ _ hγ x hx
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hγx := (uHGroup _ _ hH).2.1 γ hγ x hx
  refine ⟨norm_Dmin_le k r z z' hγ hx, div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, fun H₁ hH₁ => ?_⟩
  · refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    have := gramProj_le k r hj z hγx (Ppos k r z z' γ x)
    simpa only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec] using this
  · refine (Finset.fold_max_le _).2 ⟨le_max_left _ _, fun l _ => le_max_of_le_right ?_⟩
    exact div_le_div_of_nonneg_right (norm_Dmin_le k r z z' hγ hx l) (by positivity)

end GlobalTheory.Amp.MinorBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourStepsStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowAnalyticFacts_of_four_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP → StepAnalyticP := by
  first | exact @GlobalTheory.NGRow.stepAnalyticP_of_steps | exact GlobalTheory.NGRow.stepAnalyticP_of_steps | (intros; apply GlobalTheory.NGRow.stepAnalyticP_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfStepsStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps : StepAnalyticConstantsP → StepSizes → StepClass → StepNormals → StepPoints → StepHeight → NGCut2P := by
  first | exact @GlobalTheory.NGRow.ngCut2P_of_steps | exact GlobalTheory.NGRow.ngCut2P_of_steps | (intros; apply GlobalTheory.NGRow.ngCut2P_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepStep

theorem step_bound (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hM : 0 ≤ M)
    (hb : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro y hy u hu
  have hvv : ∀ z : B.I.GA, ‖vv B Fr u z‖ = Real.sqrt (∑ i, ‖Fr i u z‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hvvs : ∀ z : B.I.GA, ‖vv B Fr u z - vv B Fr u x‖ = Real.sqrt (∑ i, ‖Fr i u z - Fr i u x‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hnear := GlobalTheory.T.representativeValuesVector_variation_unipotentOrbit B b ρ M P D T Fr x W hS hR hM hb
  have hcusp := GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable B
  obtain ⟨L, hL, -, -, hLf⟩ := hcusp
  have hrep : ∀ i, GlobalTheory.Dec.IsContRep B (T i u) (Fr i u) := fun i => (hR i P u hu).1
  have hx : ‖vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    rw [hvv]
    refine GlobalTheory.MeanZero.norm_le_of_cusp B.I B.μf B.g W D (fun i => Fr i u) x (fun i => Fr i u x) _ hg hW ?_ ?_
    · intro i
      obtain ⟨hc, hl, hae⟩ := hrep i
      refine ⟨hc, hl, (hR i P u hu).2.1, ?_⟩
      have h1 := ((GlobalTheory.T.continuous_representative_properties B).2.2.2 _ _ (hrep i)).1
      exact (hLf (T i u) (Fr i u) hl hc h1).1 ((hL _).2 (hC i u))
    · intro ν hν
      obtain ⟨γ, hγ, k, hk, z, hz, he⟩ := hcov ν hν
      have hval : ∀ i, Fr i u (((ν, 1) : B.I.GA) * x) = Fr i u z := by
        intro i
        rw [he, (hR i P u hu).2.1 k hk, (hrep i).2.1 γ hγ]
      simp only [hval]
      rw [← hvvs]
      exact hnear z hz u hu
  calc ‖vv B Fr u y‖ = ‖(vv B Fr u y - vv B Fr u x) + vv B Fr u x‖ := by rw [sub_add_cancel]
    _ ≤ ‖vv B Fr u y - vv B Fr u x‖ + ‖vv B Fr u x‖ := norm_add_le _ _
    _ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ + ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ :=
        add_le_add (hnear y hy u hu) hx
    _ = 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by ring

end GlobalTheory.DeepStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExists
section
noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fundC_holds : FundC := by
  intro D X Y u t
  obtain ⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t
  set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0
  refine ⟨K, hK.1, fun r _ => ?_⟩
  obtain ⟨s0, hs0, hs0F⟩ := hK.2.1 r
  refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
  have h2 : (s0 * s'⁻¹) * (s' * r) ∈ K := by simpa [mul_assoc] using hs0F
  have := hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
  exact (mul_inv_eq_one.1 this).symm

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ d d' : LocNG.Datum P, LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ P.Hp = S.Hp ∧ (P.PrimeTo → S.Hp = 1) ∧ ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) := by
  first | exact @GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | exact GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps | (intros; apply GlobalTheory.HL.WCoordTerms.terms_orbits_heights_amps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_conjugation : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), (∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ γ ∈ GQ B, d.chr ψ γ = 1 ∧ ∀ f, IsThetaFun ψ L A f → d.jac ψ γ f 0 = f 0) ∧ Continuous (d.chr ψ)) ∧ Continuous d.aCo ∧ Continuous d.tCo ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.aCo (g * n * g⁻¹) = (Formalism.L2.Theta.mt A h).mulVec (d.aCo n) ∧ d.tCo (g * n * g⁻¹) = d.tCo n ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (g * n * g⁻¹) = d.chr ψ n := by
  first | exact @GlobalTheory.HeisCoord.coords_laws | exact GlobalTheory.HeisCoord.coords_laws | (intros; apply GlobalTheory.HeisCoord.coords_laws <;> assumption)
end

