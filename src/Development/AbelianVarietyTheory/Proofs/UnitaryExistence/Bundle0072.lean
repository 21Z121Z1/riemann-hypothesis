import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetNeZeroOfOrth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  first | exact @GlobalTheory.UnitaryGlue.adelic_glue | exact GlobalTheory.UnitaryGlue.adelic_glue | (intros; apply GlobalTheory.UnitaryGlue.adelic_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicPoints_moduli_every_place : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → AlgPtLa Xo c := by
  first | exact @GlobalTheory.algPtLa_moduli | exact GlobalTheory.algPtLa_moduli | (intros; apply GlobalTheory.algPtLa_moduli <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplicationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  first | exact @GlobalTheory.CompRat.Acts.main | exact GlobalTheory.CompRat.Acts.main | (intros; apply GlobalTheory.CompRat.Acts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def archHom (V : HSp D) (τ : D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  if h : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ then
    h.choose.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (infHom V))
  else 1

theorem archHom_eq (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) : archHom V τ g = Pj.archM V θ g := by
  have h' : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := ⟨θ, h⟩
  rw [archHom, dif_pos h', GlobalTheory.LettersCheck.isInfEmb_unique τ _ θ h'.choose_spec h]
  rfl

theorem isHermitian_gram (V : HSp D) (τ : D.host.E →+* ℂ) : (V.gram.map τ).IsHermitian := by
  ext a b
  have h := V.herm.eq (V.frame b) (V.frame a)
  show star (τ (V.hT (V.frame b) (V.frame a))) = τ (V.hT (V.frame a) (V.frame b))
  rw [← h]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem lintegral_adelic (V : HSp D) {Comp : Type} [Fintype Comp] {r : ℕ} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt (X k) (F k) := by
  subst hr
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : μ.IsMulRightInvariant := ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) μ h𝓕 h0 h1⟩
  have hmem : ∀ h, h ∈ (Kf.map (finHom V)).comap (finHom V) ↔ ∃ a ∈ GinfC V, ∃ z ∈ Kf, h = a * z := by
    intro h
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨h * z⁻¹, ?_, z, hz, (inv_mul_cancel_right _ _).symm⟩
      show finHom V (h * z⁻¹) = 1
      rw [map_mul, map_inv, e, mul_inv_cancel]
    · rintro ⟨a, ha, z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [map_mul, show finHom V a = 1 from ha, one_mul]
  have hopen : IsOpen (((Kf.map (finHom V)).comap (finHom V) : Subgroup (GA D V)) : Set (GA D V)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK 1) ?_)
    rintro _ ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [one_mul, map_mul, show finHom V a = 1 from ha, mul_one]
  have hg := fun k => (GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have ha : ∀ k (τ : (X k).Ψ) g, archHom V τ.1 g = Pj.archM V (th k τ) g := fun k τ g => archHom_eq V (hth k τ) g
  have htr : ∀ (u J : Matrix (Fin V.rank) (Fin V.rank) ℂ), uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ ↔
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u J
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨dL, dR, ⟨x0, d0, dI⟩, dD, -, dF⟩ := hd
  refine lintegral_dict X μ (GQ V) (GinfC V) Kf _ h𝓕 h0 h1 hopen.measurableSet hmem dict (archHom V)
    (fun τ => (V.gram.map τ)ᵀ) x0 hΨ (fun τ => ⟨(isHermitian_gram V τ).transpose, ?_⟩) (fun k τ => ?_)
    (fun k τ g => ?_) (fun k u hu => ?_) (fun k τ z hz => ?_) (fun k γ hγ h => ?_) dL dR d0 (fun g h hh => ?_) dD dF hU
  · rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)
  · exact ((hg k).2.2.1 τ).congr fun g => (ha k τ g).symm
  · rw [htr, ha]
    exact GlobalTheory.RecDictModel.archM_unitary V (hth k τ) g
  · obtain ⟨h, hh, e⟩ := (hg k).2.2.2 u fun τ => (htr _ _).1 (hu τ)
    exact ⟨h, hh, fun τ => (ha k τ h).trans (e τ)⟩
  · rw [ha, Pj.archM, show infHom V z = 1 from ((hK z).1 hz).1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ (X k).Ψ
      · exact ⟨⟨τ, hτ⟩⟩
      · exact ⟨⟨_, not_not.1 (mt ((X k).cmType τ).2 hτ)⟩⟩
    obtain ⟨γ₀, -, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have e1 : (matHom V γ).1 = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) := (congrArg Units.val e0).symm
    have e2 : Pj.archM V (th k τ) γ = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
      have : ((γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (th k τ) =
          (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
        ext i j
        exact (hth k τ).1 _
      rw [← this, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
      rfl
    have e3 : (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 := by
      refine Matrix.map_injective τ.1.injective ?_
      show (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1
      rw [← e2, ← ha, h τ, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Subtype.ext (Units.ext (e1.trans ?_))
    rw [e3]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · simp only [ha]
    exact dI g h hh

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Pj.Unf Xo c σ r)

theorem measurable_onQ_adel (V : HSp D) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hm : Pj.MuUnit V dict mu) (hc : Continuous mu) (P : Pj.FDSec X) (hP : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) :
    Measurable (Pj.onQ V (Pj.adel V dict mu P)) := by
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((hK k).1 hk).1)
    (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK) fun k τ => ⟨τ.1, hth k τ⟩
  have hC : Continuous fun g => mu g * P (dict g).1 (dict g).2 := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨M, hM, k, x, hx, hs⟩ := hloc g₀
    have h1 : ContinuousOn (fun g => mu g * P k (x g)) M :=
      hc.continuousOn.mul ((hP k).comp hx fun g hg => (hs g hg).1)
    refine (h1.continuousAt hM).congr ?_
    filter_upwards [hM] with g hg
    obtain ⟨hxd, γ, hγ, he⟩ := hs g hg
    rw [he]
    exact congrArg (mu g * ·) (hΓ k γ hγ _ hxd).symm
  have hL : ∀ g g', g * g'⁻¹ ∈ GQ V → mu g' * P (dict g').1 (dict g').2 = mu g * P (dict g).1 (dict g).2 := by
    intro g g' h4
    obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 g'
    have e' := hm.1 (g * g'⁻¹) g'
    rw [inv_mul_cancel_right] at e e'
    rw [hm.2.2.1 _ h4, one_mul] at e'
    rw [e, e']
    exact congrArg (mu g' * ·) (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  rw [measurable_from_quotient]
  have : (Pj.onQ V (Pj.adel V dict mu P) ∘ Quotient.mk'') = fun g => mu g * P (dict g).1 (dict g).2 :=
    funext fun g => hL g (Pj.autMk V g).out (QuotientGroup.rightRel_apply.1 (Quotient.mk_out g))
  rw [this]
  exact hC.measurable

end GlobalTheory.PeterssonCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_pushInvertible_over_completeDVR : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  first | exact @GlobalTheory.exists_model_pushInvertible_under_cdvr | exact GlobalTheory.exists_model_pushInvertible_under_cdvr | (intros; apply GlobalTheory.exists_model_pushInvertible_under_cdvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponent
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem normConst_pos_of_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    0 < normConst ty ξ₀ := by
  unfold normConst
  refine Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))
  have := norm_pos_iff.mpr ((map_ne_zero (ty j)).mpr h)
  positivity

theorem exists_isNormUn : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∃ un, IsNormUn T un := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T
  have key : ∀ x : (M.X k).dom, ∃ y : FrPt Xo c (CAt σ), ∃ κ : ℂ,
      κ ^ 2 = (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ∧
        IsThetaPt T (T.co.symm x.1) κ y := by
    intro x
    have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
      simpa using x.2
    have hne : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (normConst_pos_of_ne_zero _ (M.X k).ξ0_ne).ne')
        (T.norm _ hb).1.ne_zero
    obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
      ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det) (n := 2) two_pos
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hκ]; simp)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_isThetaPt' hS E H Dw l Xo c σ g e F r M k T _ hb κ hκ0
    exact ⟨y, κ, hκ, hy⟩
  choose un hun using key
  exact ⟨un, hun⟩

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfNonemptyFrame
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory

theorem exists_unf_nonempty_frame : N1c → Out.SecTwistSt → ∀ (D : D7) (Q : Par D), (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Nonempty (Data D.host.E D.R.r) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty (Σ k, Frame (U.X k).Ψ D.R.r) := by
  intro hN hT D Q h hX j σ
  obtain ⟨X⟩ := hX
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex hN hT _ _ (Q.Dw j) _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨⟨(), fun _ => 0⟩⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.NonzeroGenerates

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem spMap_id' {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) :=
  Spec.map_id (CommRingCat.of A)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S T U : Type} [CommRing S] [CommRing T] [CommRing U]

theorem eq_id_comp (x : Sp S ⟶ Xo.X) : x = spMap (RingHom.id S) ≫ x := by
  rw [spMap_id', Category.id_comp]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) : scal x (a * b) i = scal x a i * scal x b i :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 a b i).1

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 1 1 i).2.2

theorem secBC_id_iff (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.1 a s t

theorem exists_mul (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) :
    ∃ t : LB.Sec (PPx x), ∀ i, t.f i = scal x a i * s.f i := by
  obtain ⟨t, ht, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) a x x (eq_id_comp x) s
  exact ⟨t, (secBC_id_iff x a s t).1 ht⟩

theorem exists_pull (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (hx : x' = spMap φ ≫ x)
    (s : LB.Sec (PPx x)) : ∃ s' : LB.Sec (PPx x'), SecBC φ 1 x x' s s' :=
  (GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ 1 x x' hx s).exists

theorem pull_trans_iff {φ : S →+* T} {ψ : T →+* U} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} {x'' : Sp U ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) (hx' : x'' = spMap ψ ≫ x') {a : S} {s s' s''} (h : SecBC φ a x x' s s') :
    SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'' :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T U φ ψ x x' x'' hx hx').1 a s s' s'' h

theorem pull_mul_iff {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') :
    SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T T φ _ x x' x' hx (eq_id_comp x')).2.2.1 a s s' t' h

theorem pull_iff_of_mul {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s t : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (hst : ∀ i, t.f i = scal x a i * s.f i)
    (h : SecBC φ 1 x x' s s') : SecBC φ 1 x x' t t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i := by
  rw [pull_trans_iff (eq_id_comp x) hx ((secBC_id_iff x a s t).2 hst), RingHom.comp_id, pull_mul_iff hx h]

theorem not_mem_of_mem_basicOpen_scal (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) (q : Gx x)
    (hq : q ∈ (Gx x).basicOpen (scal x a i)) : a ∉ (Formalism.L2.PjFree.gxSnd x q).asIdeal := by
  have e : scal x a i = ((Formalism.L2.PjFree.gxSnd x).appLE ⊤ ((PPx x).U i) le_top).hom (toΓ S a) := rfl
  rw [e] at hq
  erw [Scheme.basicOpen_appLE] at hq
  have h2 := hq.2
  have e2 : (Sp S).basicOpen (toΓ S a) = PrimeSpectrum.basicOpen a :=
    basicOpen_eq_of_affine (R := CommRingCat.of S) a
  erw [e2] at h2
  exact h2

theorem secGen_of_secGen {x : Sp S ⟶ Xo.X} {θ s : LB.Sec (PPx x)} (hθ : SecGen x θ) (hs : SecNZ x s) :
    SecGen x s := by
  obtain ⟨a, ha, -⟩ := hθ s
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hn
    obtain ⟨q, i, hq, hqi⟩ := hs ⟨m, hm.isPrime⟩
    rw [ha i, Scheme.basicOpen_mul] at hqi
    have := not_mem_of_mem_basicOpen_scal x a i q hqi.1
    rw [hq] at this
    exact this ham
  obtain ⟨u, rfl⟩ := hu
  intro t
  obtain ⟨b, hb, hbu⟩ := hθ t
  refine ⟨b * ↑u⁻¹, fun i => ?_, fun c hc => ?_⟩
  · rw [hb i, ha i, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right]
  · have : c * u = b := hbu _ fun i => by rw [hc i, ha i, ← _root_.mul_assoc, ← scal_mul]
    rw [← this, Units.mul_inv_cancel_right]

theorem secNZ_pull {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') (hs : SecNZ x s) : SecNZ x' s' :=
  fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo S T φ x x' hx s s' h p').2 (hs _)

theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr
  exact funext h

end GlobalTheory.Frames.NonzeroGenerates

open GlobalTheory.Frames.NonzeroGenerates in

theorem GlobalTheory.Frames.secGen_of_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecNZ x s → SecGen x s := by
  intro hBC E _ _ _ H Dw l Xo S _ x s hs t
  classical

  let G : Set S := {g | ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (φ : S →+* T),
    ψ.comp (algebraMap S (Localization.Away g)) = φ → ∀ s' : LB.Sec (PPx (spMap φ ≫ x)),
      SecBC φ 1 x _ s s' → SecGen _ s'}
  have hG : Ideal.span G = ⊤ := by
    by_contra hn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hBC E H Dw l Xo S x ⟨m, hm.isPrime⟩
    refine hg (hle (Ideal.subset_span ?_))
    intro T _ ψ φ hφ s' hs'
    have e : spMap φ ≫ x = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x := by
      rw [← hφ, spMap_comp', Category.assoc]
    obtain ⟨θ', hθ'⟩ := exists_pull ψ _ _ e θ
    exact secGen_of_secGen (hθ T ψ _ θ' e hθ').1 (secNZ_pull rfl hs' hs)
  choose sl hsl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl s
  choose tl htl using fun g : S => exists_pull (algebraMap S (Localization.Away g)) x _ rfl t
  have hgen : ∀ g : G, SecGen _ (sl g) := fun g => g.2 _ (RingHom.id _) _ (RingHom.id_comp _) _ (hsl g)
  choose c hc hcu using fun g : G => hgen g (tl g)
  have key : ∀ (g : G) (h : S) (α : Localization.Away g.1 →+* Localization.Away h),
      α.comp (algebraMap S _) = algebraMap S _ →
      ∀ i, (tl h).f i = scal _ (α (c g)) i * (sl h).f i := by
    intro g h α hα
    have e : spMap (algebraMap S (Localization.Away h)) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away g.1)) ≫ x := by
      rw [← hα, spMap_comp', Category.assoc]
    have h1 : SecBC α 1 _ _ (sl g) (sl h) := (pull_trans_iff rfl e (hsl g)).2 (by rw [hα]; exact hsl h)
    have h2 : SecBC α 1 _ _ (tl g) (tl h) := (pull_trans_iff rfl e (htl g)).2 (by rw [hα]; exact htl h)
    exact (pull_iff_of_mul e (hc g) h1).1 h2
  obtain ⟨a, ha, hau⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top G hG c (fun g h => by
    have hα : (IsLocalization.Away.awayToAwayRight (S := Localization.Away g.1)
        (P := Localization.Away (g.1 * h.1)) g.1 h.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq g.1 h.1 r
    have hβ : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away h.1)
        (P := Localization.Away (g.1 * h.1)) h.1 g.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq h.1 g.1 r
    exact (g.2 _ _ _ hα _ (hsl _) (tl _)).unique (key g _ _ hα) (key h _ _ hβ))
  refine ⟨a, ?_, fun b hb => hau b fun g => hcu g _ ((pull_iff_of_mul rfl hb (hsl g)).1 (htl g))⟩
  obtain ⟨t₀, ht₀⟩ := exists_mul x a s
  have hloc : ∀ g : G, SecBC (algebraMap S (Localization.Away g.1)) 1 x _ t₀ (tl g) := fun g =>
    (pull_iff_of_mul rfl ht₀ (hsl g)).2 (by rw [ha g]; exact hc g)
  obtain ⟨F, hF, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hG)
  let h : Fin F.card → S := fun i => (F.equivFin.symm i).1
  have hr : Set.range h = F := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (F.equivFin.symm i).2
    · intro hy
      exact ⟨F.equivFin ⟨y, hy⟩, by simp [h]⟩
  have hh : Ideal.span (Set.range h) = ⊤ := by
    rw [hr]; exact (Ideal.eq_top_iff_one _).2 h1
  have hmem : ∀ i, h i ∈ G := fun i => hF (F.equivFin.symm i).2
  have glue := GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x F.card h hh (fun i => tl (h i)) (fun i j α β hα hβ u hu => by
    have e1 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away (h i))) ≫ x := by
      rw [← hα, spMap_comp', Category.assoc]
    have e2 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap β ≫ spMap (algebraMap S (Localization.Away (h j))) ≫ x := by
      rw [← hβ, spMap_comp', Category.assoc]
    have h3 := (pull_trans_iff rfl e1 (htl (h i))).1 hu
    rw [hα] at h3
    exact (pull_trans_iff rfl e2 (htl (h j))).2 (by rw [hβ]; exact h3))
  have : t = t₀ := glue.unique (fun i => htl (h i)) (fun i => hloc ⟨h i, hmem i⟩)
  rw [this]
  exact ht₀
end
end

