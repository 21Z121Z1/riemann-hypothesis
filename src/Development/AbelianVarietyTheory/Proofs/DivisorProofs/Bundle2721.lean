import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodula
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCover
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CoverPull

theorem cusp_pullback_existsUnique : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  intro D T j Y e o hT hj hG hu hm a n hD f hf
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', hbc⟩ := GlobalTheory.T.moduliLaws_coefficientFieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hf', -⟩ := hbc a n hD ⟨f, hf⟩
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hu hm
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  rw [cuspW_wtZ] at hf hf'
  have hs := cusp_le_sec _ _ _ a n hf
  have hs' := cusp_le_sec _ _ _ a n hf'
  obtain ⟨g, ⟨hg, hgP⟩, huniq⟩ := (GlobalTheory.CoverSec.section_pullback_existsUnique _ _ _ _ _ _ Y.d hpq.2 hG.lev.1
    (Or.inl ⟨hpq.1, hL.levA⟩) a n).1 _ hs'
  refine ⟨g, ⟨?_, (hP a n f hs g).2 hgP⟩, fun g' hg' => huniq g' ⟨?_, (hP a n f hs g').1 hg'.2⟩⟩
  · rw [Deep.V, cuspW_wtZ]
    exact (GlobalTheory.T.cuspForm_iff_levelCover_pullback D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n hD hD.2 _ hs' g hg hgP).2 hf'
  · have h := hg'.1
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h

end GlobalTheory.CoverPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DVRExt

theorem exists_unique_extend : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  intro R _ P W L _ _ _ _ _ _ f x
  haveI : ValuationRing W := inferInstance
  have hv : ValuativeCriterion P.A.hom := by
    have h : IsProper P.A.hom := P.isAb.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x.left ≫ P.A.hom = spMap (algebraMap W L) ≫ spMap f := by
    rw [Over.w x]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let S : ValuativeCommSq P.A.hom :=
    { R := W, K := L, i₁ := x.left, i₂ := spMap f, commSq := ⟨hsq⟩ }
  have hU := (hv S).some
  refine ⟨Over.homMk hU.default.l hU.default.fac_right, hU.default.fac_left, ?_⟩
  intro y hy
  have hy2 : y.left ≫ P.A.hom = spMap f := Over.w y
  let T : S.commSq.LiftStruct := ⟨y.left, hy, hy2⟩
  have hT : T = hU.default := hU.uniq T
  apply Over.OverMorphism.ext
  change T.l = hU.default.l
  rw [hT]

end GlobalTheory.DVRExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomOfLinearMapKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HomAlgAny

open MeasureTheory

theorem surjective_of_forall_sub_mem {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : DiscreteTopology Λ) (h : ∀ x, ∃ z, x - T z ∈ Λ) : Function.Surjective T := by
  by_contra hT
  have hV : (LinearMap.range T).restrictScalars ℝ ≠ ⊤ := by
    intro h'
    apply hT
    intro x
    have hx : x ∈ (LinearMap.range T).restrictScalars ℝ := h' ▸ Submodule.mem_top
    exact LinearMap.mem_range.1 ((Submodule.restrictScalars_mem ℝ _ x).1 hx)
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcov : (Set.univ : Set (Fin g → ℂ)) ⊆ ⋃ l : Λ,
      (fun y => y + -(l : Fin g → ℂ)) ⁻¹' (((LinearMap.range T).restrictScalars ℝ : Submodule ℝ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
    intro x _
    obtain ⟨z, hz⟩ := h x
    refine Set.mem_iUnion.2 ⟨⟨x - T z, hz⟩, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact ⟨z, by abel⟩
  have h0 : volume (Set.univ : Set (Fin g → ℂ)) = 0 :=
    measure_mono_null hcov (measure_iUnion_null fun l => by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hV)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) h0

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a b : Fin g → ℂ)
    (h : u.ex a = u.ex b) : a - b ∈ u.Λ := by
  rw [← u.ker]
  have e := u.ex_add (a - b) b
  rw [sub_add_cancel, h] at e
  have e2 := congrArg (· * (u.ex b)⁻¹) e
  simpa using e2.symm

theorem exists_of_polAV (P P' : Out.PolAV (Sp ℂ)) (n n' : ℕ) (v : HolUnif P.A P.L n) (v' : HolUnif P'.A P'.L n')
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)) (hn : P.g = n) (hn' : P'.g = n') (hF : ∀ z ∈ v.Λ, F z ∈ v'.Λ) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, v'.ex (F z) = v.ex z ≫ f := by
  subst hn hn'
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := existsUnique_isMonHom_of_map_lattice hL hL2 AbLaw.CubeAssembly.cube_gen
    thetaUnifAV_all P P' P.L P'.L v v' F hF
  exact ⟨f, hf, hfe⟩

open GlobalTheory.HolUnifEnd GlobalTheory.HolUnifHom in

theorem exists_isMonHom_of_map_lattice (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g g' : ℕ)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hgA : SmoothOfRelativeDimension g A.hom)
    (hgA' : SmoothOfRelativeDimension g' A'.hom) (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hM : ∀ x ∈ u.Λ, M x ∈ u'.Λ) :
    ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g' hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := exists_of_polAV Q Q' (8 * g) (8 * g') v v' (J' ∘ₗ M ∘ₗ R) hQ hQ'
    (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

theorem existsUnique_isMonHom_of_map_ker : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  intro A A' _ _ _ _ g g' hA hA' hg hg' e e' M he he' hM
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨L', ⟨u'⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A' g' hA' hg'
  obtain ⟨t1, t2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨t1', t2'⟩ := GlobalTheory.TorusTransfer.tangent_bijective u' hg'
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u t1 t2 e he.1 he.2.2.1
  obtain ⟨T', hT', -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g' u' t1' t2' e' he'.1 he'.2.2.1
  have hTs : Function.Surjective T := surjective_of_forall_sub_mem T u.Λ u.discrete fun x => by
    obtain ⟨z, hz⟩ := he.2.1 (u.ex x)
    exact ⟨z, sub_mem_of_ex_eq u _ _ (by rw [hT]; exact hz.symm)⟩
  have hTi : Function.Injective T := LinearMap.injective_iff_surjective.2 hTs
  let Te : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
  have hTe : ∀ z, Te.symm (T z) = z := fun z => Te.symm_apply_apply z
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := T' ∘ₗ M ∘ₗ Te.symm.toLinearMap
  have hFT : ∀ z, F (T z) = T' (M z) := fun z => by simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, hTe]
  have hF : ∀ x ∈ u.Λ, F x ∈ u'.Λ := fun x hx => by
    obtain ⟨z, rfl⟩ := hTs x
    rw [hFT, ← u'.ker, hT']
    refine hM z ?_
    rw [← hT, u.ker]
    exact hx
  obtain ⟨α, hα, hαe⟩ := exists_isMonHom_of_map_lattice A A' g g' hA hA' hg hg' L L' u u' F hF
  have hex : ∀ z, e' (M z) = e z ≫ α := fun z => by
    rw [← hT', ← hFT, hαe, hT]
  refine ⟨α, ⟨hα, hex⟩, fun f hf => ?_⟩
  haveI := hA.smooth
  haveI := hA'.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
  obtain ⟨z, rfl⟩ := he.2.1 x
  rw [← hf.2, hex]

end GlobalTheory.HomAlgAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunctionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_section_of_natural_pointwise_function : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) → ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → evU z.left U a = t E z := by
  first | exact @GlobalTheory.PtExt.NatSec.exists_unique_section | exact GlobalTheory.PtExt.NatSec.exists_unique_section | (intros; apply GlobalTheory.PtExt.NatSec.exists_unique_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ValPt

theorem exists_unique_stalk_hom : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  intro X x p _ y hy
  subst hy
  refine ⟨(Scheme.stalkClosedPointTo y).hom, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y, ?_⟩
  intro g hg
  have hpt : (X.fromSpecStalk (y (cPt p))) ((spMap g) (cPt p)) =
      (X.fromSpecStalk (y (cPt p))) (closedPoint (X.presheaf.stalk (y (cPt p)))) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact congrArg (fun f : Sp (OO p) ⟶ X => f (cPt p)) hg
  have hinj : Function.Injective (X.fromSpecStalk (y (cPt p))) :=
    (X.fromSpecStalk (y (cPt p))).isEmbedding.injective
  have hloc : IsLocalHom g := by
    rw [isLocalHom_iff_comap_closedPoint]
    exact hinj hpt
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of (OO p))).symm.injective
    (a₁ := ⟨y (cPt p), CommRingCat.ofHom g, hloc⟩)
    (a₂ := ⟨y (cPt p), Scheme.stalkClosedPointTo y, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
        exact hg.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  exact congrArg CommRingCat.Hom.hom e3

end GlobalTheory.ValPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodulaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_datum_standardLattice_tensor_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ g s : ℕ, r = s * Module.finrank ℚ E → ∃ (Dm : Datum H) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), Dm.p = s * g ∧ Dm.q = s * g ∧ (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) ∧ ∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1) := by
  first | exact @GlobalTheory.UnitaryStd.exists_datum | exact GlobalTheory.UnitaryStd.exists_datum | (intros; apply GlobalTheory.UnitaryStd.exists_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitPullAct

theorem mono_spMap_toRat {o Ω F : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field F] [CharZero F] (R : Subalgebra o Ω)
    (s : Sp (ratHull R) ⟶ Sp F) : Mono (spMap (toRat R)) := by
  haveI : CharZero Ω :=
    (RingHom.charZero_iff ((ratHull R).val.toRingHom.comp (Spec.preimage s).hom).injective).1 inferInstance
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  infer_instance

theorem exists_pull_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : UTrait Xo c) :
    ∃ ψ : T.P.A.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback T.P.A.A Xo.univ.t.G (T.y ≫ pullback.fst _ _) ψ ∧
      LBIso T.P.A.L (Xo.univ.t.PP.L.pull ψ) ∧
      ∀ a : 𝓞 E, (T.P.oA.act a).left ≫ ψ = ψ ≫ (Xo.univ.t.act.act a).left := by
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hm := T.P.U.gen_hom
  haveI : IsMonHom T.P.U.gen.symm.hom := inferInstanceAs (IsMonHom T.P.U.gen.inv)
  have hgen : IsGrpPullback T.P.A.A T.t.G (jK T.V) (T.P.U.gen.inv.left ≫ pullback.fst T.t.G.hom (jK T.V)) :=
    ((isGrpPullback_of_iso T.P.U.gen.symm).comp (isGrpPullback_pullback T.t.G (jK T.V))).congr (Category.id_comp _) rfl
  obtain ⟨e, he, he₁⟩ := grpPullback_iso hgen m₁.cart
  haveI := he
  refine ⟨e.hom.left ≫ m₂.cm.F, ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · have hext : LBIso (T.t.PP.L.pull (pullback.fst T.t.G.hom (jK T.V))) (T.P.A.L.pull T.P.U.gen.hom.left) := by
      obtain ⟨w, hw⟩ := T.P.U.ext
      have hb := T.P.bundle
      exact LBIso.symm (hb ▸ ⟨w, hw⟩)
    have s1 := GlobalTheory.TripleTheta.lbIso_inv T.P.U.gen hext
    have s2 := (GlobalTheory.GenSpread.lbIso_pull_pull T.t.PP.isLB (a := pullback.fst T.t.G.hom (jK T.V))
      T.P.U.gen.inv.left rfl).symm
    have s3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₁) e.hom.left he₁.symm
    have s4 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₂) e.hom.left rfl
    exact LBIso.trans T.P.A.isLB (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB Xo.univ.t.PP.isLB _) s1
      (LBIso.trans (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB T.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) s2
      (LBIso.trans (pull_isLB T.t.PP.isLB _) (pull_isLB tK.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) (LBIso.symm s3) s4))
  · letI := H.starRing
    have h0 := T.P.lin.ext a
    have h1 : T.P.oA.act a ≫ T.P.U.gen.inv = T.P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (T.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
      exact h0
    have h2 : ((Over.pullback (jK T.V)).map (T.t.act.act a)).left ≫ pullback.fst T.t.G.hom (jK T.V) =
        pullback.fst T.t.G.hom (jK T.V) ≫ (T.t.act.act a).left := pullback.lift_fst _ _ _
    have h3 : (T.P.oA.act a).left ≫ e.hom.left = e.hom.left ≫ (tK.act.act a).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, m₁.act a, ← Category.assoc e.hom.left, he₁, ← Category.assoc,
          ← Over.comp_left, h1, Over.comp_left, Category.assoc, h2, Category.assoc]
      · rw [← Over.comp_left, ← Over.comp_left, Over.w, Over.w]
    rw [← Category.assoc, h3, Category.assoc, m₂.act a, Category.assoc]

theorem exists_pull_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ S ρ u' G _ α β hα hβ hL T yK hy
  obtain ⟨ψ, hψ, hψL, hψa⟩ := exists_pull_univ T
  have e₀ : T.y ≫ pullback.fst _ _ = spMap yK ≫ u' ≫ pullback.fst _ _ := by rw [← hy, Category.assoc]
  have w₀ : ψ ≫ Xo.univ.t.G.hom = (T.P.A.A.hom ≫ spMap yK) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← e₀]; exact hψ.1.w
  have e₁ := hβ.1.lift_fst _ _ w₀
  have hγ := hβ.cancel (hψ.congr e₀ e₁.symm) (hβ.1.lift_snd _ _ w₀)
  generalize hβ.1.lift _ _ w₀ = γ at e₁ hγ
  refine ⟨γ ≫ α, (hγ.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl, ?_, fun Y x x' w w' a hw hw' h => ?_⟩
  · exact LBIso.trans T.P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB ρ.P.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp γ rfl e₁.symm hL).symm
  · haveI := mono_spMap_toRat S.R (u' ≫ pullback.snd _ _)
    haveI : Mono α := ⟨fun f g hfg => hα.1.hom_ext hfg ((cancel_mono (spMap (toRat S.R))).1 (by
      rw [Category.assoc, Category.assoc, ← hα.1.w, ← Category.assoc, hfg, Category.assoc]))⟩
    obtain rfl : w = x.left ≫ γ := (cancel_mono α).1 (hw.trans (Category.assoc _ _ _).symm)
    obtain rfl : w' = x'.left ≫ γ := (cancel_mono α).1 (hw'.trans (Category.assoc _ _ _).symm)
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψa a, ← e₁]
      simpa only [Category.assoc] using h
    · rw [Over.w, Over.w]

end GlobalTheory.UPoinc.TraitPullAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBySecBZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.WeightZero

open GlobalTheory.ProjSpace GlobalTheory.AbLaw GlobalTheory.Cartier

theorem veryAmpleBy_of_sval {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}
    (g : Z ⟶ Y) [IsIso g] (f : Y ⟶ Sp R) {m : ℕ} (s : Fin (m + 1) → (LB.LinComb L φ ε).Sec)
    (t : Fin (m + 1) → (LB.LinComb L φ' ε').Sec)
    (h : ∀ i z J, Good L z J → sval (t i) (𝟙 Z) z J = sval (s i) g z J) (hs : VeryAmpleBy f _ s) :
    VeryAmpleBy (g ≫ f) _ t := by
  obtain ⟨hc, hi⟩ := (veryAmpleBy_iff f s).1 hs
  have key : ∀ z : Z, ∃ (W : Z.Opens) (_ : z ∈ W) (k : (LB.LinComb L φ ε).ι)
      (hk : W ≤ g ⁻¹ᵁ (LB.LinComb L φ ε).U k) (l : (LB.LinComb L φ' ε').ι) (hl : W ≤ (LB.LinComb L φ' ε').U l),
      ∀ j, resG Z hl ((t j).f l) = (g.appLE _ W hk).hom ((s j).f k) := by
    intro z
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
    refine ⟨LB.wchart L φ' (fun k => J (𝟙 Z ≫ φ' k)) ⊓ g ⁻¹ᵁ LB.wchart L φ (fun k => J (g ≫ φ k)),
      ⟨Good.mem hJ φ' (𝟙 Z), Good.mem hJ φ g⟩, fun k => J (g ≫ φ k), inf_le_right, fun k => J (𝟙 Z ≫ φ' k),
      inf_le_left, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨J', hJ', e⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k))
      (fun a => J (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k) a)) (fun a b e => congrArg J e) (by
        rintro (a | a)
        exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have e₁ := h j y J' hJ'
    rw [sval_of (t j) _ y J' _ (fun k => e (.inl k)), sval_of (s j) _ y J' _ (fun k => e (.inr k))] at e₁
    refine (gs_res _ y _ hy _).trans (e₁.trans (Eq.symm ?_))
    exact (gs_res (𝟙 Z) y inf_le_right hy _).trans (gs_pull (𝟙 Z) g y _ hy.2 _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine _root_.top_le_iff.1 fun z _ => ?_
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g z)))
    have h₁ : z ∈ Z.basicOpen (resG Z hl ((t i).f l)) := by
      rw [e i, Scheme.basicOpen_appLE]
      exact ⟨hz, (mem_nonzeroLocus_iff _ k (hk hz)).1 hi⟩
    rw [Scheme.basicOpen_res] at h₁
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, basicOpen_le_nonzeroLocus _ l h₁.2⟩
  refine (veryAmpleBy_iff _ t).2 ⟨ht, ?_⟩
  rw [toProj_eq_comp_of_locally hc g ht fun z => by
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    exact ⟨W, hz, k, hk, l, hl, 1, fun j => (e j).trans (_root_.one_mul _).symm⟩]
  infer_instance

theorem formEq_weight_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (fun _ : Fin k => 𝟙 D.P.A.left) (fun _ => 1) (D.famφB 0) (DegPre.famε k) := by
  intro U _ h
  have h0 : D.c 0 = 1 := by
    have h : D.c 0 = D.c 0 * D.c 0 := by
      have := D.c_add 0 0
      rwa [add_zero] at this
    exact mul_eq_left.1 h.symm
  have h1 : toUnit D.P.A ≫ D.c 0 = 1 := by rw [h0, comp_one]
  have h2 : toUnit D.P.A ≫ η[D.P.A] = 1 := rfl
  have h3 : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 _ := _root_.mul_one (𝟙 D.P.A)
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, h1, h2, h3]
  simp [zpow_sub]

theorem exists_veryAmpleBy_secB_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ)
    (hk : 4 ≤ k) : ∃ (m : ℕ) (s : Fin (m + 1) → D.SecB k 0), VeryAmpleBy D.P.A.hom _ s := by
  obtain ⟨m, s, H⟩ := (GlobalTheory.allSixLaws.1.ample (Sp R) D.P k hk).2 ⊤ (isAffineOpen_top _)
  have : IsIso (⊤ : (Sp R).Opens).ι := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have : IsIso (D.P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso D.P.A.left.topIso.hom)
  have h' := (veryAmpleBy_comp_iff (D.P.A.hom ∣_ ⊤) (⊤ : (Sp R).Opens).ι s).2 H
  rw [morphismRestrict_ι] at h'
  let ψ := inv (D.P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (D.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  choose s' hs' using fun i => exists_sec_pull (L := D.P.L) _ _ (s i) ψ (fun _ : Fin k => 𝟙 D.P.A.left) fun _ => hψ.symm
  choose t ht using fun i => exists_sec D.P.isLB (formEq_weight_zero D k) (s' i)
  have := veryAmpleBy_of_sval D.P.isLB ψ _ s t (fun i z J hJ => by
    refine (ht i _ _ z J hJ).trans ((hs' i _ z _ (hJ.mem _ _)).trans ?_)
    rw [Category.id_comp, sval_of (s i) ψ z J (fun _ => J (𝟙 _ ≫ 𝟙 _)) fun _ => by rw [hψ, Category.id_comp]]) h'
  rw [← Category.assoc, hψ, Category.id_comp] at this
  exact ⟨m, t, this⟩

end GlobalTheory.Mum.WeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentEstimateFromLanglands
section
set_option autoImplicit false

namespace GlobalTheory.BigOn

theorem expSt_of_hypotheses :
    GlobalTheory.Published.ClozelCohomological →
      GlobalTheory.Published.CohomologicalCsdTempered →
      GlobalTheory.Published.HeckeLAdicCharacter →
      GlobalTheory.Published.ChebotarevDegreeOne →
      GlobalTheory.Published.DiscreteSpectrumGL →
      GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
      GlobalTheory.Published.BaseChangeDefiniteUnitary →
      GlobalTheory.Published.BhattScholzeCrystallineLattices →
      GlobalTheory.Published.HeckeLAdicCharacterAbove →
      GlobalTheory.Published.LocalLanglandsGL →
      GlobalTheory.BigOn.ExpSt :=
  fun hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hLL =>
    GlobalTheory.T.expansion_of_numerics_model GlobalTheory.T.weylLattice_exact_exponent_block_cut GlobalTheory.ExpTie.numSt GlobalTheory.T.sum_expansion_statement
      (GlobalTheory.T.model_statement_of_frame_galois hBS hCheb GlobalTheory.T.SmallStatement (GlobalTheory.T.FrameStatement GlobalTheory.T.SmallStatement)
        (GlobalTheory.T.galois_statement_of_small hCoh hTemp hHecke hCheb hDisc hGal hBC hBS hAbove hLL GlobalTheory.T.SmallStatement))

end GlobalTheory.BigOn
end

