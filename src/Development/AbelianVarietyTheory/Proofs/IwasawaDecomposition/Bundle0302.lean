import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

theorem exists_log_adicAbv_eq_single (F : Type) [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) :
    ∃ (H : ℕ) (π : 𝓞 F), 0 < H ∧ π ≠ 0 ∧
      Real.log (NumberField.HeightOneSpectrum.adicAbv F u (algebraMap (𝓞 F) F π)) =
        -(H : ℝ) * Real.log (Ideal.absNorm u.asIdeal : ℝ) ∧
      ∀ v, v ≠ u →
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F π)) = 0 := by
  classical
  set H := Fintype.card (ClassGroup (𝓞 F)) with hH
  have hu : u.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero u.ne_bot
  have hp : u.asIdeal ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hu H
  have h1 : ClassGroup.mk0 ⟨u.asIdeal ^ H, hp⟩ = 1 := by
    have : (⟨u.asIdeal ^ H, hp⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨u.asIdeal, hu⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := ((ClassGroup.mk0_eq_one_iff hp).1 h1).principal
  have hπ' : u.asIdeal ^ H = Ideal.span {π} := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero H u.ne_bot hπ'
  refine ⟨H, π, Fintype.card_pos, hπ0, ?_, fun v hv => ?_⟩
  · have hval : u.valuation F (algebraMap (𝓞 F) F π) = WithZero.exp (-(H : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, u.intValuation_if_neg hπ0, ← hπ',
        Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 u.ne_bot) u.associates_irreducible,
        Associates.count_self u.associates_irreducible, mul_one]
    have h0 : u.valuation F (algebraMap (𝓞 F) F π) ≠ 0 := by rw [hval]; exact WithZero.exp_ne_zero
    rw [NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
    have : Multiplicative.toAdd (WithZero.unzero h0) = -(H : ℤ) := by
      simp only [hval]; rfl
    rw [this]
    simp [Real.log_inv, Real.log_pow]
  · have hn : π ∉ v.asIdeal := by
      intro hm
      have : u.asIdeal ^ H ≤ v.asIdeal := by
        rw [hπ', Ideal.span_singleton_le_iff_mem]; exact hm
      have h2 : u.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le this
      exact hv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    have : NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F π) = 1 :=
      (v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hn
    rw [this, Real.log_one]

theorem exists_mul_eq_log_adicAbv_sub (F : Type) [Field F] [NumberField F]
    (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : (Function.support c).Finite)
    (hq : ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧
      (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) :
    ∃ (h : ℕ+) (b b' : 𝓞 F), b ≠ 0 ∧ b' ≠ 0 ∧ ∀ v, ((h : ℕ) : ℝ) * c v =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) -
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
  classical
  have hlog : ∀ (v : HeightOneSpectrum (𝓞 F)) (x y : 𝓞 F) (k l : ℕ), x ≠ 0 → y ≠ 0 →
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F (x ^ k * y ^ l))) =
        k * Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x)) +
        l * Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F y)) := by
    intro v x y k l hx hy
    have hne : ∀ x : 𝓞 F, x ≠ 0 →
        NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≠ 0 := fun x hx =>
      (AbsoluteValue.ne_zero_iff _).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx)
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow,
      Real.log_mul (pow_ne_zero _ (hne x hx)) (pow_ne_zero _ (hne y hy)), Real.log_pow, Real.log_pow]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ (h : ℕ) (b b' : 𝓞 F), 0 < h ∧ b ≠ 0 ∧ b' ≠ 0 ∧
      ∀ v, (h : ℝ) * (if v ∈ S then c v else 0) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) -
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, 1, 1, one_pos, one_ne_zero, one_ne_zero, fun v => by simp⟩
    | insert u S hu ih =>
      obtain ⟨h, b, b', hh, hb, hb', hS⟩ := ih
      obtain ⟨m, z, hm, hz⟩ := hq u
      obtain ⟨H, π, hH, hπ, h1, h2⟩ := exists_log_adicAbv_eq_single F u
      refine ⟨h * (m * H), b ^ (m * H) * π ^ (h * (-z).toNat), b' ^ (m * H) * π ^ (h * z.toNat),
        by positivity, mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ hπ),
        mul_ne_zero (pow_ne_zero _ hb') (pow_ne_zero _ hπ), fun v => ?_⟩
      rw [hlog v _ _ _ _ hb hπ, hlog v _ _ _ _ hb' hπ]
      have hv := hS v
      have hz' : ((z.toNat : ℕ) : ℝ) - (((-z).toNat : ℕ) : ℝ) = z := by
        have := Int.toNat_sub_toNat_neg z
        exact_mod_cast this
      by_cases hvu : v = u
      · subst hvu
        rw [if_neg hu] at hv
        rw [if_pos (Finset.mem_insert_self _ _), h1]
        push_cast
        linear_combination (m * H : ℝ) * hv + (h * H : ℝ) * hz -
          (h * H * Real.log (Ideal.absNorm v.asIdeal : ℝ)) * hz'
      · simp only [Finset.mem_insert, hvu, false_or]
        rw [h2 v hvu]
        push_cast
        linear_combination (m * H : ℝ) * hv
  obtain ⟨h, b, b', hh, hb, hb', hS⟩ := key hc.toFinset
  refine ⟨⟨h, hh⟩, b, b', hb, hb', fun v => ?_⟩
  rw [← hS v]
  by_cases hv : v ∈ hc.toFinset
  · rw [if_pos hv]; rfl
  · rw [if_neg hv]
    have : c v = 0 := by simpa using hv
    simp [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DenseCompl

open scoped WithZeroTopology in

theorem exists_extension_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (he : 0 < e)
    (hv : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧
      (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first
  | exact @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | (apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom ..)

end GlobalTheory.DenseCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricActionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_half_realisation_geometric_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  first | exact @GlobalTheory.RealGeo.exists_geoHalf_geoR | exact GlobalTheory.RealGeo.exists_geoHalf_geoR | (intros; apply GlobalTheory.RealGeo.exists_geoHalf_geoR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodIntegralFormsLatticeBaseLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.GoodLatFree

theorem mem_of_span {S V H : Type} [Semiring S] [AddCommGroup V] [Module S V] [AddCommGroup H] [Module ℂ H]
    (f : V →+ H) (τ : S → ℂ) (hfs : ∀ (b : S) (x : V), f (b • x) = τ b • f x) (P : Submodule ℂ H) (X : Set V)
    (hX : ∀ x ∈ X, f x ∈ P) : ∀ v ∈ Submodule.span S X, f v ∈ P := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add _ _ _ _ h1 h2 => rw [map_add]; exact P.add_mem h1 h2
  | smul b x _ h => rw [hfs]; exact P.smul_mem _ h

theorem int_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    {iZ : Module ℤ V} (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) :
    ∀ v ∈ @Submodule.span ℤ V _ _ iZ X, j v ∈ P := by
  obtain rfl : iZ = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  exact mem_of_span j.toAddMonoidHom (fun n : ℤ => (n : ℂ)) (fun n x => by
    show j (n • x) = (n : ℂ) • j x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]) P X hX

theorem ring_span {L V H : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span (𝓞 L) X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : 𝓞 L => σ (a : L)) (fun a x => by
    show j (a • x) = σ (a : L) • j x
    rw [← algebraMap_smul L a x, map_smulₛₗ]) P X hX

theorem field_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span L X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : L => σ a) (fun a x => j.map_smulₛₗ a x) P X hX

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩

set_option maxHeartbeats 2000000 in

theorem exists_oLat_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (E : M →ₗ[ℂ] (R.toRealDat.HW i (sg0 D A3.A)).H), Function.Injective E → LinearMap.range E = (R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.toRealDat.HW i (sg0 D A3.A)).e → ∃ L : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) M, ∀ x, x ∈ L.carrier ↔ ∃ v ∈ (R.toRealDat.FW i).MK, v ∈ (R.toRealDat.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧ E x = (R.toRealDat.FW i).j (sg0 D A3.A) v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO _ hP hH i M _ _ _ E hinj hrange
  classical
  have hI := hH.aux.integral i
  have hχ := chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG hP hH i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1) hχ F.lv2.P0 F.lv2.ψ0⁻¹
    (fun g => (idemOf A3.A.X).coeff g) (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]⟩
  have hsa : ∀ a, sg0 D A3.A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]

  obtain ⟨S0, hS0⟩ := GlobalTheory.GoodLatDescent.fg_MK_good (R.FW i) hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
  have hfg : ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))).restrictScalars ℤ).FG :=
    Submodule.FG.restrictScalars ⟨S0, rfl⟩
  obtain ⟨T0, hT0⟩ := hfg
  have hT : ∀ y, y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) ↔
      y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
    intro y
    rw [hT0]
    show y ∈ ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))) : Set _) ↔ _
    rw [hS0]; rfl

  have hWS : LinearMap.range E = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hrange]; exact (hH.aux.levelW false i _).symm
  have hjW : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ LinearMap.range E := by
    intro y hy
    rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i]
    have hyW : y ∈ R.toRealDat.WL F.lv2 false i := hy
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).repr ⟨y, hyW⟩ k •
        R.toRealDat.bL F.lv2 false i k = y := by
      have h := congrArg (R.toRealDat.WL F.lv2 false i).subtype
        ((Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).sum_repr ⟨y, hyW⟩)
      rw [map_sum] at h
      exact h
    rw [← hs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ, ← GlobalTheory.Mem.LiftTheta.goodForm_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

  have hex : ∀ t, ∃ x : M, t ∈ T0 → E x = (R.FW i).j (sg0 D A3.A) t := by
    intro t
    by_cases ht : t ∈ T0
    · obtain ⟨x, hx⟩ := hjW t ((hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))).2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose g hg using hex

  have hA : ∀ y, y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) →
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    have h1 : y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := (hT y).2 hy
    have h2 : ∀ x ∈ (T0 : Set (Fin (R.nW i) → D.what₂.LL)), (R.FW i).j (sg0 D A3.A) x ∈
        Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) :=
      fun x hx => Submodule.subset_span (Set.mem_image_of_mem _ hx)
    have h1' : y ∈ @Submodule.span ℤ (Fin (R.nW i) → D.what₂.LL) _ _ (AddCommGroup.toIntModule _) (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := by
      convert h1
    have h3 := int_span (L := D.what₂.LL) (V := Fin (R.nW i) → D.what₂.LL) (iZ := AddCommGroup.toIntModule _) ((R.FW i).j (sg0 D A3.A)) (T0 : Set _) _ h2
    exact h3 y h1'
  have hB : ∀ y ∈ (R.FW i).Mj F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← hspan] at hy
    exact ring_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hA x hx) y hy
  have hC : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← (GlobalTheory.GoodLat.mj_full (R.FW i) hI.1 hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)).2] at hy
    exact field_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hB x hx) y hy
  have hgen : Submodule.span ℂ ((T0.image g : Finset M) : Set M) = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_top, Submodule.map_span, Finset.coe_image, Set.image_image]
    have him : (fun t => E (g t)) '' (T0 : Set _) = (R.FW i).j (sg0 D A3.A) '' (T0 : Set _) :=
      Set.image_congr fun t ht => hg t ht
    rw [him]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact hjW t ((hT t).1 (Submodule.subset_span ht)).2
    · rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe]
      beta_reduce
      rw [GlobalTheory.Mem.LiftTheta.goodForm_single]
      exact hC _ (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i) k).2
  refine ⟨⟨T0.image g, hgen⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨c, rfl⟩
    rw [map_sum]
    refine Finset.sum_induction _
      (fun w => ∃ v ∈ (R.FW i).MK, v ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧
        w = (R.FW i).j (sg0 D A3.A) v) ?_ ?_ ?_
    · rintro _ _ ⟨v1, h1, h1', rfl⟩ ⟨v2, h2, h2', rfl⟩
      exact ⟨v1 + v2, Submodule.add_mem _ h1 h2, Submodule.add_mem _ h1' h2', (map_add _ _ _).symm⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, (map_zero _).symm⟩
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have htg := (hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))
      obtain ⟨k, hk⟩ := hO (c (g t))
      have hint : IsIntegral ℤ k := by
        have h1 : IsIntegral ℤ (D.what₂.OtoLL (c (g t))) := D.O_int (c (g t))
        rw [← hk] at h1
        exact (isIntegral_algHom_iff (algebraMap Ks D.what₂.LL).toIntAlgHom (algebraMap Ks D.what₂.LL).injective).1 h1
      let kk : 𝓞 Ks := ⟨k, hint⟩
      have hkk : D.what₂.OtoLL (c (g t)) • t = kk • t := by
        rw [← hk, algebraMap_smul, ← algebraMap_smul Ks kk t]
        rfl
      refine ⟨D.what₂.OtoLL (c (g t)) • t, ?_, Submodule.smul_mem _ _ htg.2, ?_⟩
      · rw [hkk]; exact Submodule.smul_mem _ _ htg.1
      · rw [map_smul, hg t ht, map_smulₛₗ, hsa]
        rfl
  · rintro ⟨v, hv1, hv2, hxv⟩
    obtain ⟨n, -, hn⟩ := Submodule.mem_span_finset.1 ((hT v).2 ⟨hv1, hv2⟩)
    have hx : x = ∑ t ∈ T0, ((n t : ℤ) : ℂ) • g t := by
      apply hinj
      rw [hxv, ← hn, map_sum, map_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_zsmul, map_smul, hg t ht, Int.cast_smul_eq_zsmul]
    refine ⟨fun y => ∑ t ∈ T0 with g t = y, (n t : D.what₂.O), ?_⟩
    rw [hx]
    symm
    refine Finset.sum_image' _ fun t _ => ?_
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t' ht' => ?_
    rw [(Finset.mem_filter.1 ht').2, map_intCast]

end GlobalTheory.Mem.GoodLatFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_unipB_mul_diagT_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  intro k _ _ _ _ m g
  obtain ⟨u, l, w, hw, h⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (points (Fin m)) g
  refine ⟨u, u.2, (leviTorus k (Fin m)).symm l, w, hw, ?_⟩
  rw [h]
  simp [diagT]

end GlobalTheory.SmGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.CoordW

set_option maxHeartbeats 2000000 in

theorem exists_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ mj : GlobalTheory.RealGeo.MjTie R.toRealDat F.lv2, ∃ jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1), ∀ (i : Fin D.R.m) v, mj.eW i (jW i v) = (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) v) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH mj
  have key : ∀ i : Fin D.R.m, ∃ g : (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL]
      D.what₂.Mj ((i : ℕ) + 1), ∀ v, mj.eW i (g v) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v := by
    intro i
    have he : Function.Injective (mj.eW i) :=
      GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (mj.eW_norm i)
    have hspan : Submodule.span ℂ (Set.range fun k =>
        GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1)) = LinearMap.range (mj.eW i) :=
      (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
        ((hH.aux.levelW false i _).trans (mj.eW_range i).symm)
    have hmem : ∀ v, GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v ∈ LinearMap.range (mj.eW i) := by
      intro v
      rw [← hspan, GlobalTheory.Mem.LiftTheta.semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    choose s hs using fun v => LinearMap.mem_range.1 (hmem v)
    exact ⟨{ toFun := s
             map_add' := fun a b => he ((hs (a + b)).trans (((map_add _ a b).trans
               (congrArg₂ (· + ·) (hs a).symm (hs b).symm)).trans (map_add (mj.eW i) (s a) (s b)).symm))
             map_smul' := fun c a => he ((hs (c • a)).trans (((LinearMap.map_smulₛₗ _ c a).trans
               (congrArg (D.what₂.embLL c • ·) (hs a).symm)).trans (LinearMap.map_smul (mj.eW i) _ (s a)).symm)) }, hs⟩
  choose jW hjW using key
  exact ⟨jW, fun i v => (hjW i v).trans
    (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _).symm)⟩

end GlobalTheory.Mem.CoordW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_congruence_in_level_character_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  first | exact @GlobalTheory.LevFinCong.exists_finCong_lev | exact GlobalTheory.LevFinCong.exists_finCong_lev | (intros; apply GlobalTheory.LevFinCong.exists_finCong_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegralStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsLattice F Λ ∧ ∀ γ : GL (Fin n) F, (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) → s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  first | exact @GlobalTheory.StabLat.exists_lattice_stab_conj | exact GlobalTheory.StabLat.exists_lattice_stab_conj | (intros; apply GlobalTheory.StabLat.exists_lattice_stab_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroRationalLiftMemBasePartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  first | exact @GlobalTheory.RatLift.exists_rat_lift_mem_part | exact GlobalTheory.RatLift.exists_rat_lift_mem_part | (intros; apply GlobalTheory.RatLift.exists_rat_lift_mem_part <;> assumption)
end

