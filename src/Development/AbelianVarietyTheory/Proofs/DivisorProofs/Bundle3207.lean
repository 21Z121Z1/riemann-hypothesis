import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3173
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.NotRelAmpleOfNotIsProper
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PowPolarizationIsoPullbackOfDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAevalTraceFormLeFibreValuesStatement
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_aeval_traceForm_le_fibreValues : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) → ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ), (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T → ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 → (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) → ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  first | exact @GlobalTheory.HSAmp.norm_aeval_trace_le | exact GlobalTheory.HSAmp.norm_aeval_trace_le | (intros; apply GlobalTheory.HSAmp.norm_aeval_trace_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingAdjointInvolution
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_adjoint_involution : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  first | (exact @GlobalTheory.LKGeo.adj_actOn_afP) | (exact GlobalTheory.LKGeo.adj_actOn_afP) | (intros; apply GlobalTheory.LKGeo.adj_actOn_afP  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationTopChernDensityEqFactorialMixedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_topChernDensity_eq_factorial_mixed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  first | exact @GlobalTheory.Mix.pol_chernDens_comb | exact GlobalTheory.Mix.pol_chernDens_comb | (intros; apply GlobalTheory.Mix.pol_chernDens_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianIsoDescendsFromAlgebraicExtensio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.Spread GlobalTheory.HomPairDescent

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem model_descends : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K), (∀ z : K, ∃ f : Polynomial k, f ≠ 0 ∧ Polynomial.eval₂ σ z f = 0) → ∀ (B₁ B₂ : PolAV (Sp k)) (P₀ : PolAV (Sp K)) (c₁ : P₀.A.left ⟶ B₁.A.left) (c₂ : P₀.A.left ⟶ B₂.A.left), IsGrpPullback P₀.A B₁.A (spMap σ) c₁ → IsGrpPullback P₀.A B₂.A (spMap σ) c₂ → LBIso P₀.L (B₁.L.pull c₁) → LBIso P₀.L (B₂.L.pull c₂) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (C : PolAV (Sp k₁)) (χ : C.A.left ⟶ B₁.A.left), IsGrpPullback C.A B₁.A (spMap α) χ → LBIso C.L (B₁.L.pull χ) → ∃ χ₂ : C.A.left ⟶ B₂.A.left, IsGrpPullback C.A B₂.A (spMap α) χ₂ ∧ LBIso C.L (B₂.L.pull χ₂) ∧ ∀ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ → d ≫ C.A.hom = P₀.A.hom ≫ spMap β → d ≫ χ₂ = c₂ := by
  classical
  intro k K _ _ σ hσ B₁ B₂ P₀ c₁ c₂ h₁ h₂ hL₁ hL₂
  letI : Algebra k K := σ.toAlgebra
  haveI := B₁.isAb.proper
  haveI := B₂.isAb.proper
  haveI := B₁.isAb.smooth
  haveI := B₂.isAb.smooth
  have g₁ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₁.A) B₁.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₁.A (spMap σ)
  have g₂ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₂.A) B₂.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₂.A (spMap σ)
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso h₁ g₁
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso h₂ g₂
  let f := e₁.inv ≫ e₂.hom
  let r := e₂.inv ≫ e₁.hom
  have mf : IsMonHom f := inferInstance
  obtain ⟨sf, hsf⟩ := exists_descend B₁.A B₂.A f
  obtain ⟨sr, hsr⟩ := exists_descend B₂.A B₁.A r
  let L₁ : IntermediateField k K := IntermediateField.adjoin k ((sf ∪ sr : Finset K) : Set K)
  have hL : ((sf ∪ sr : Finset K) : Set K) ⊆ L₁ := IntermediateField.subset_adjoin _ _
  obtain ⟨θf, hθf⟩ := hsf L₁ ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨θr, hθr⟩ := hsr L₁ ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have gA := isGrpPullback_bcMap B₁.A L₁.val
  have gB := isGrpPullback_bcMap B₂.A L₁.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L₁ K L₁.val.toRingHom
  haveI := (hepi _ _ _ _ _ gA.1).1
  haveI := (hepi _ _ _ _ _ gB.1).1
  haveI mθ : IsMonHom θf := (hmon _ _ _ _ _ _ θf f gA gB hθf).1 mf
  have r1 : θf ≫ θr = 𝟙 _ := by
    have := comp_eq_pow_of_epi gA hθf hθr 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  have r2 : θr ≫ θf = 𝟙 _ := by
    have := comp_eq_pow_of_epi gB hθr hθf 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  let θ : (Over.pullback (spMap (algebraMap k L₁))).obj B₁.A ≅ (Over.pullback (spMap (algebraMap k L₁))).obj B₂.A :=
    ⟨θf, θr, r1, r2⟩
  haveI : IsMonHom θ.hom := mθ
  haveI := m₁
  let φP : P₀.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left :=
    e₁.hom.left ≫ bcMap B₁.A.hom L₁.val
  have hφP : IsGrpPullback P₀.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap L₁.val.toRingHom) φP :=
    ((isGrpPullback_of_iso e₁).comp gA).congr (Category.id_comp _) rfl
  have hfst : φP ≫ pullback.fst _ _ = c₁ := by
    simp only [φP, Category.assoc, bcMap_fst]; exact he₁
  have hc₂ : φP ≫ θf.left ≫ pullback.fst _ _ = c₂ := by
    simp only [φP, Category.assoc]
    rw [reassoc_of% hθf, bcMap_fst]
    show e₁.hom.left ≫ (e₁.inv ≫ e₂.hom).left ≫ _ = _
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id_assoc, he₂]
  have HP : LBIso (B₁.L.pull c₁) (B₂.L.pull c₂) :=
    LBIso.trans (pull_isLB B₁.isLB c₁) P₀.isLB (pull_isLB B₂.isLB c₂) hL₁.symm hL₂
  have HX := LBIso.chartPull
    (chartPullOut B₁.L (fun _ => pullback.fst B₁.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP (fun _ => c₁)
      (fun _ => hfst.symm))
    (chartPullOut B₂.L (fun _ => θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP
      (fun _ => c₂) (fun _ => hc₂.symm)) HP
  obtain ⟨s₂, hs₂⟩ := lbIso_descends_to_subfield_containing_finset L₁ K L₁.val.toRingHom
    ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) P₀.A φP
    (B₁.L.pull (pullback.fst B₁.A.hom (spMap (algebraMap k L₁))))
    (B₂.L.pull (θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁)))) hφP.1
    (by change QuasiCompact (pullback.snd _ _); infer_instance)
    (by change QuasiSeparated (pullback.snd _ _); infer_instance) (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) HX
  refine ⟨sf ∪ sr ∪ s₂, ?_⟩
  intro k₁ _ α β hαβ hs C χ hχ hCL
  let E : IntermediateField k K :=
    { β.fieldRange with algebraMap_mem' := fun r => RingHom.mem_fieldRange.2 ⟨α r, RingHom.congr_fun hαβ r⟩ }
  have hle : L₁ ≤ E := IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨y, hy⟩ := hs (Finset.coe_subset.2 Finset.subset_union_left hx)
    exact RingHom.mem_fieldRange.2 ⟨y, hy⟩
  have hran : ∀ x : L₁, ∃ y, β y = x := fun x => RingHom.mem_fieldRange.1 (hle x.2)
  choose ρ₀ hρ₀ using hran
  let α₁ : L₁ →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hα₁β : β.comp α₁ = L₁.val.toRingHom := RingHom.ext fun x => hρ₀ x
  have hα₁ : α₁.comp (algebraMap k L₁) = α := RingHom.ext fun r => β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  have hsp : spMap α₁ ≫ spMap (algebraMap k L₁) = spMap α := by rw [spMap_comp', hα₁]
  have hw : χ ≫ B₁.A.hom = (C.A.hom ≫ spMap α₁) ≫ spMap (algebraMap k L₁) := by
    rw [hχ.1.w, Category.assoc, hsp]
  let j : C.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left := pullback.lift χ (C.A.hom ≫ spMap α₁) hw
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = C.A.hom ≫ spMap α₁ := pullback.lift_snd _ _ _
  have hj : IsGrpPullback C.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap α₁) j :=
    (isGrpPullback_pullback B₁.A _).cancel (hχ.congr hsp.symm hj₁.symm) hj₂
  refine ⟨j ≫ θf.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · exact (hj.comp ((isGrpPullback_of_iso θ).comp (isGrpPullback_pullback B₂.A _))).congr
      (by rw [Category.id_comp, hsp]) rfl
  · have H := hs₂ k₁ α₁ β hα₁β ((Finset.coe_subset.2 Finset.subset_union_right).trans hs) C.A j hj.1
    have H' : LBIso (B₁.L.pull χ) (B₂.L.pull (j ≫ θf.left ≫ pullback.fst _ _)) :=
      LBIso.chartPull
        (chartPullSame B₁.L (fun _ => χ) (fun _ => j ≫ pullback.fst _ _) (fun _ => 1) (𝟙 _)
          (fun _ => by rw [Category.id_comp, hj₁]))
        (chartPullSame B₂.L (fun _ => j ≫ θf.left ≫ pullback.fst _ _) (fun _ => j ≫ θf.left ≫ pullback.fst _ _)
          (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]))
        (LBIso.chartPull (chartPullIn B₁.L (fun _ => pullback.fst _ _) (fun _ => 1) j)
          (chartPullIn B₂.L (fun _ => θf.left ≫ pullback.fst _ _) (fun _ => 1) j) H)
    exact LBIso.trans C.isLB (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) hCL H'
  · intro d hd₁ hd₂
    have hdj : d ≫ j = φP := by
      apply pullback.hom_ext
      · rw [Category.assoc, hj₁, hd₁, hfst]
      · rw [Category.assoc, hj₂, ← Category.assoc, hd₂, Category.assoc, spMap_comp', hα₁β]
        exact hφP.1.w.symm
    rw [reassoc_of% hdj]
    exact hc₂

end GlobalTheory.PolIsoDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPointLiftsThroughIntermediatePul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLift

theorem lift_of_pullback_comp : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  intro S₀ S₁ S₂ f₁ f₂ A B P b a hB hP
  have w : a ≫ A.A.hom = (P.A.hom ≫ f₂) ≫ f₁ := by
    rw [hP.1.w, Category.assoc]
  refine ⟨hB.1.lift a (P.A.hom ≫ f₂) w, hB.1.lift_fst _ _ w, hB.1.lift_snd _ _ w, ?_, ?_⟩
  · exact IsGrpPullback.cancel hB (hP.congr rfl (hB.1.lift_fst _ _ w).symm) (hB.1.lift_snd _ _ w)
  · intro hPa hBb
    have e : hB.1.lift a (P.A.hom ≫ f₂) w ≫ b = a := hB.1.lift_fst _ _ w
    have h2 : LBIso (B.L.pull (hB.1.lift a (P.A.hom ≫ f₂) w)) (A.L.pull a) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B.L _ _ rfl)
        (chartPullSame A.L (fun _ => a) (fun _ => b) _ _ fun _ => e.symm) hBb
    exact LBIso.trans P.isLB (pull_isLB A.isLB a) (pull_isLB B.isLB _) hPa h2.symm

end GlobalTheory.PolLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianRelDimEqOfGrpPullbackField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDim

theorem g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (S : Scheme.{0}) (f : Sp K ⟶ S) (P : PolAV S)
    (P' : PolAV (Sp K)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → P'.g = P.g := by
  intro K _ S f P P' φ h
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)
  have hd : SmoothOfRelativeDimension P.g P'.A.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g) h.1 P.smoothDim
  obtain ⟨s⟩ : Nonempty (Sp K) := inferInstance
  exact GlobalTheory.PolTest.dim_eq_of_nonempty s P' hd

end GlobalTheory.PolDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorTau.factor_tau_pull | exact GlobalTheory.FactorTau.factor_tau_pull | (intros; apply GlobalTheory.FactorTau.factor_tau_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebungStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n)), (∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) → χ ^ p = 0 := by
  first | exact @GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung | exact GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung | (intros; apply GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowPolarizationIsoPullbackOfDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.pow_polarization_iso_pullback_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ B) (fun a g => g ≫ act'.act a) (fun n g g' z => Out.WeilIs B (P'.pull (lift (𝟙 B) (𝟙 B)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  first | exact @UpperTheory.Cb.pow_polarization_iso_pullback_of_descent | exact UpperTheory.Cb.pow_polarization_iso_pullback_of_descent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumSumSnd

theorem adj_snd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ :=
  GlobalTheory.MumProdSwap.adj_snd

end GlobalTheory.MumSumSnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunctionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  first | exact @GlobalTheory.CurveProd.product_formula_curve | exact GlobalTheory.CurveProd.product_formula_curve | (intros; apply GlobalTheory.CurveProd.product_formula_curve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstantsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_charZero_functionField_injective_constants : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  first | exact @GlobalTheory.isArithVar_charZero_functionField_and_injective | exact GlobalTheory.isArithVar_charZero_functionField_and_injective | (intros; apply GlobalTheory.isArithVar_charZero_functionField_and_injective <;> assumption)
end

