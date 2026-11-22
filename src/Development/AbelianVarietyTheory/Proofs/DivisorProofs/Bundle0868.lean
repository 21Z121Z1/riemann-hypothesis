import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume
section
open MeasureTheory

namespace GlobalTheory.HaarFundDom

open scoped Pointwise

theorem exists_haar_fundDom_mass_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K →
    (∀ g : G, ∃ γ : Γ, γ • g ∈ K) →
    ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ _ K hK hcov
  let μ₀ : Measure G := Measure.haar
  obtain ⟨𝓕, h𝓕m, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hD : IsFundamentalDomain Γ 𝓕 μ₀ := IsFundamentalDomain.mk' h𝓕m.nullMeasurableSet h𝓕
  haveI : MeasurableMul G :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul Γ G :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : G => (γ : G) * x).measurable⟩
  haveI : SMulInvariantMeasure Γ G μ₀ := ⟨fun γ A _ => measure_preimage_mul μ₀ (γ : G) A⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • K ∩ 𝓕 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set.2 ⟨γ • x, hγ, ?_⟩, hx⟩
    simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hfin : μ₀ 𝓕 < ⊤ :=
    calc μ₀ 𝓕 ≤ μ₀ (⋃ γ : Γ, γ • K ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ₀ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ₀ K := (hD.measure_eq_tsum _).symm
      _ < ⊤ := hK.measure_lt_top
  have hne : μ₀ 𝓕 ≠ 0 := by
    intro h0
    have h1 := hD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter, measure_smul, h0, tsum_zero] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne μ₀)).ne' h1
  refine ⟨(μ₀ 𝓕)⁻¹ • μ₀, 𝓕, ?_, hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hne)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]

end GlobalTheory.HaarFundDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
section
namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilProdEqOneOfToric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud.ProdToric

theorem isMonHom_lift_id_one {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (𝟙 G) (1 : G ⟶ G')) := by
  rw [Hom.one_def]; infer_instance

theorem isMonHom_lift_one_id {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (1 : G' ⟶ G) (𝟙 G')) := by
  rw [Hom.one_def]; infer_instance

end GlobalTheory.Raynaud.ProdToric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatFramedOfGramPosDef
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem datFramed_of_gram_posDef {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok)
    (hG : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef) : DatFramed S h := by
  refine ⟨S.hDim h, (S.hB h).equivFun.symm, fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v),
    fun v => (frameOfSpec _ _ (GlobalTheory.PeriodClassSum.gramAt_posDef S h v (hG v))).1, fun v x => ?_⟩
  have h1 := (GlobalTheory.PeriodClassSum.isFormsOf_formsLat S h hG ⊥).2 v ((S.hB h).equivFun.symm x)
  have h2 : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (S.hDim h))) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v x =
      Formalism.HermitianLatticesTheory.normAt (S.hB h) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v ((S.hB h).equivFun.symm x) := by
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    congr 2
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [h2]
  exact h1

theorem evGSD_datFramed : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (h : (evGSD W Ch sel mu P u).Ok), DatFramed (evGSD W Ch sel mu P u) h := by
  intro X _ Pr R W Ch sel Sg mu P u h
  refine datFramed_of_gram_posDef _ h fun v => ?_
  have e : (evGSD W Ch sel mu P u).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u R.m) := by
    ext i k
    show pairVr X.emb (W.lamTrue u R.m) 1 (bVV _ _ i) (bVV _ _ k) = _
    rw [GlobalTheory.ColNorms.pairVr_one_eq]
    exact GlobalTheory.PeriodClassSum.pairK_one_basis (W.lamTrue u R.m) i k
  rw [e]
  exact GlobalTheory.PeriodClassSum.gramB_posDef (W.lamTrue u R.m) v.embedding

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

theorem descend_point_to_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  intro V K W L _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomm hloc X x f hxf
  classical

  let c : Sp W := IsLocalRing.closedPoint W
  obtain ⟨U, hU, hcU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show f c ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hfU : ∀ a : Sp W, f a ∈ U := fun a =>
    ((IsLocalRing.specializes_closedPoint (R := W) a).map f.continuous).mem_open U.isOpen hcU
  have hrf : Set.range f ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    exact hfU a
  let pL : Sp L := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have e := congrArg (fun h : Sp L ⟶ X => h pL) hxf
    simp only [Scheme.Hom.comp_apply] at e
    have ha : a = (spMap (algebraMap K L)) pL := by
      have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
      exact PrimeSpectrum.ext ((h a).trans (h _).symm)
    rw [ha, e]
    exact hfU _
  have hf₁ := IsOpenImmersion.lift_fac hU'.fromSpec f hrf
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec f hrf)] at hf₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set β := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec f hrf) with hβ
  set α := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hα
  have key : α ≫ CommRingCat.ofHom (algebraMap K L) = β ≫ CommRingCat.ofHom (algebraMap W L) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hx₁, hf₁]
    exact hxf
  have key' : ∀ r, algebraMap K L (α.hom r) = algebraMap W L (β.hom r) := fun r => by
    have e := congrArg (fun h => h.hom r) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using e

  have hmem : ∀ r, α.hom r ∈ (algebraMap V K).range := by
    intro r
    by_cases h0 : α.hom r = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger V (α.hom r) with ⟨v, hv⟩ | ⟨b, hb⟩
    · exact ⟨v, hv⟩
    · by_cases hb0 : IsUnit b
      · obtain ⟨u, rfl⟩ := hb0
        refine ⟨((u⁻¹ : Vˣ) : V), ?_⟩
        rw [← inv_inv (α.hom r), ← hb]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      · exfalso
        apply hb0
        apply (isUnit_map_iff (algebraMap V W) b).1
        refine isUnit_iff_exists_inv.2 ⟨β.hom r, ?_⟩
        apply IsFractionRing.injective W L
        rw [map_mul, map_one, ← key', ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hb, ← map_mul,
          inv_mul_cancel₀ h0, map_one]
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h),
      (algebraMap V K).rangeRestrict_surjective⟩
  let χ : Γ(X, U) →+* V := e.symm.toRingHom.comp (α.hom.codRestrict _ hmem)
  have hχ : (algebraMap V K).comp χ = α.hom := by
    ext r
    change algebraMap V K (e.symm ⟨α.hom r, hmem r⟩) = α.hom r
    have := congrArg Subtype.val (e.apply_symm_apply ⟨α.hom r, hmem r⟩)
    exact this
  refine ⟨Spec.map (CommRingCat.ofHom χ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun h => h r) hχ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  first | (exact @GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (exact GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (intros; apply GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

def QSum {G : Type} [CommGroup G] (H : Subgroup G) (F : G → ℂ) (a : ℂ) : Prop :=
  HasSum (fun q : G ⧸ H => F q.out) a

section Generic

variable {G : Type} [CommGroup G] {H H' : Subgroup G} {F : G → ℂ} {a : ℂ}

theorem out_mk (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (g : G) : F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hu, hF _ _ u.2]

theorem QSum.translate (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) (t : G) :
    QSum H (fun g => F (t * g)) a := by
  unfold QSum at *
  rw [← (Equiv.mulLeft (QuotientGroup.mk t : G ⧸ H)).hasSum_iff] at h
  refine h.congr_fun fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ∀ g, ∀ u ∈ H, F (t * (g * u)) = F (t * g) := fun g u hu => by rw [← mul_assoc, hF _ _ hu]
  exact (out_mk (F := fun g => F (t * g)) h2 g).trans (out_mk hF (t * g)).symm

theorem QSum.eq_zero (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) {t : G} {c : ℂ} (hc : c ≠ 1)
    (ht : ∀ g, F (t * g) = c * F g) : a = 0 := by
  have h1 := h.translate hF t
  unfold QSum at *
  simp only [ht] at h1
  have h2 := h1.unique (h.mul_left c)
  have : (c - 1) * a = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem qsum_index (hle : H ≤ H') (hn : H.relIndex H' ≠ 0) (hF : ∀ g, ∀ u ∈ H', F (g * u) = F g) :
    QSum H' F a ↔ QSum H F (H.relIndex H' * a) := by
  unfold QSum
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hn⟩
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  have hc : (Fintype.card (H' ⧸ H.subgroupOf H') : ℂ) = H.relIndex H' := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hn' : (H.relIndex H' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  let e := Subgroup.quotientEquivProdOfLE hle
  have he : ∀ q : G ⧸ H, F q.out = (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [out_mk fun g u hu => hF g u (hle hu)]
    show _ = F (QuotientGroup.mk g : G ⧸ H').out * 1
    rw [out_mk hF, mul_one]
  simp only [he]
  rw [show (fun q => (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q)) =
    (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) ∘ e from rfl, e.hasSum_iff]
  have h1 : HasSum (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) (H.relIndex H') := by
    simpa [hc] using hasSum_fintype (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ))
  constructor
  · intro h
    rw [mul_comm]
    have h3 := summable_mul_of_summable_norm (f := fun q : G ⧸ H' => F q.out)
      (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h.summable.norm h1.summable.norm
    exact HasSum.mul (f := fun q : G ⧸ H' => F q.out) (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h h1 h3
  · intro h
    have h2 := (h.prod_fiberwise fun q => h1.mul_left (F q.out)).mul_right (H.relIndex H' : ℂ)⁻¹
    simp only [mul_assoc, mul_inv_cancel₀ hn', mul_one] at h2
    rwa [mul_left_comm, mul_inv_cancel₀ hn', mul_one] at h2

end Generic

variable {E : Type} [Field E] [NumberField E]

def box (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Set (Af E)ˣ :=
  {z | ∀ w, Valued.v ((z : Af E) w - 1) ≤ r w}

def congr (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Subgroup (Af E)ˣ where
  carrier := {z | ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w}
  one_mem' := fun w => by
    have : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl
    rw [this]; simp
  mul_mem' := fun {a b} ha hb w => by
    have : ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl
    rw [this]
    refine ⟨by rw [map_mul, (ha w).1, (hb w).1, one_mul], ?_⟩
    rw [show (a : Af E) w * (b : Af E) w - 1 = (a : Af E) w * ((b : Af E) w - 1) + ((a : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha w).1, one_mul]; exact (hb w).2) (ha w).2
  inv_mem' := fun {a} ha w => by
    have h : (a : Af E) w * ((a⁻¹ : (Af E)ˣ) : Af E) w = 1 := (coord w a).val_inv
    have h1 : Valued.v (((a⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by
      have := congrArg Valued.v h
      rwa [map_mul, (ha w).1, one_mul, map_one] at this
    refine ⟨h1, ?_⟩
    rw [show ((a⁻¹ : (Af E)ˣ) : Af E) w - 1 = -(((a⁻¹ : (Af E)ˣ) : Af E) w * ((a : Af E) w - 1)) by
      linear_combination h, Valuation.map_neg, map_mul, h1, one_mul]
    exact (ha w).2

theorem mem_congr {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z : (Af E)ˣ} :
    z ∈ congr r ↔ ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w := Iff.rfl

def radN (E : Type) [Field E] [NumberField E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : WithZero (Multiplicative ℤ) :=
  Valued.v (N : w.adicCompletion E)

def zterm (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : ℂ := (finPart χ z : ℂ) * ((modF z : ℝ) : ℂ) ^ s

theorem zterm_mul (χ : HChar E) (s : ℂ) (z z' : (Af E)ˣ) : zterm χ s (z * z') = zterm χ s z * zterm χ s z' := by
  unfold zterm
  rw [map_mul, ObjModel.modF_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ObjModel.modF_pos _).le (ObjModel.modF_pos _).le, Units.val_mul]
  ring

theorem differentiable_zterm (χ : HChar E) (z : (Af E)ˣ) : Differentiable ℂ fun s => zterm χ s z :=
  Differentiable.const_mul (Differentiable.const_cpow differentiable_id
    (Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))) _

theorem zterm_ne_zero (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : zterm χ s z ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))

theorem modF_eq_one {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) : modF u = 1 := by
  unfold modF
  exact finprod_eq_one_of_forall_eq_one fun v => by simp [hu v]

theorem zterm_unit (χ : HChar E) (s : ℂ) {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) :
    zterm χ s u = finPart χ u := by
  simp [zterm, modF_eq_one hu]

theorem norm_zterm {χ : HChar E} (h : IsUnitary χ) (s : ℂ) (z : (Af E)ˣ) : ‖zterm χ s z‖ = modF z ^ s.re := by
  have : ‖(finPart χ z : ℂ)‖ = 1 := h _
  rw [zterm, norm_mul, this, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ObjModel.modF_pos z)]

theorem mul_mem_box {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z u : (Af E)ˣ} (hu : u ∈ congr r) :
    z * u ∈ box r ↔ z ∈ box r := by
  have key : ∀ z u : (Af E)ˣ, u ∈ congr r → z ∈ box r → z * u ∈ box r := fun z u hu hz w => by
    have : ((z * u : (Af E)ˣ) : Af E) w = (z : Af E) w * (u : Af E) w := rfl
    rw [this, show (z : Af E) w * (u : Af E) w - 1 = (u : Af E) w * ((z : Af E) w - 1) + ((u : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (hu w).1, one_mul]; exact hz w) (hu w).2
  exact ⟨fun h => by simpa using key _ _ (inv_mem hu) h, key _ _ hu⟩

theorem congr_mono {r r' : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} (h : ∀ w, r w ≤ r' w) :
    congr r ≤ congr r' := fun _ hz w => ⟨(hz w).1, (hz w).2.trans (h w)⟩

theorem mem_hatO_of_sub {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) {a z : Af E} (ha : a ∈ hatO c)
    (hz : ∀ P, Valued.v (z P - a P) ≤ radN E n P) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - a P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) + a := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key ha

theorem congr_le_hatOUnits {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) :
    congr (radN E n) ≤ hatOUnits c := fun _ hu =>
  mem_hatOUnits.2 ⟨mem_hatO_of_sub hn hc (one_mem _) fun P => (hu P).2,
    mem_hatO_of_sub hn hc (one_mem _) fun P => (inv_mem hu P).2⟩

theorem hatOUnits_le_congr (c : Ideal (OF E)) : hatOUnits c ≤ congr (fun _ => 1) := fun u hu w => by
  have h : Valued.v ((u : Af E) w) = 1 :=
    GlobalTheory.Mem.TupHecke.valued_eq_one_of_le (coord w u) (ObjModel.hatO_integral hu.1 w) (ObjModel.hatO_integral hu.2 w)
  exact ⟨h, Valuation.map_sub_le _ h.le (by simp)⟩

end GlobalTheory.CMVal.LatEnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLastZeroInclusionStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_last_zero_inclusion : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  first | exact @GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero | exact GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero | (intros; apply GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStableStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M → (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  first | exact @GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | exact GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | (intros; apply GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylOrthonormalBasisValuesAtUnitarySumSqLeOnStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n, ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 := by
  first | exact @GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | exact GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | (intros; apply GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSpannedByInterlacingStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_spanned_by_interlacing : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg)) := by
  first | exact @GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen | exact GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen | (intros; apply GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen <;> assumption)
end

