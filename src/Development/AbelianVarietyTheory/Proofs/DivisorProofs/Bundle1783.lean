import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem indicator_mem_SB {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  have hU : {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} =
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_integer _
  have hC : IsClosed (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClosed_integer _
  have hK : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  rw [hU]
  have hUo : IsOpen (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => hO)
  have hUc : IsClosed (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isClosed_set_pi (fun _ _ => hC)
  have hUk : IsCompact (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isCompact_univ_pi (fun _ => hK)
  generalize Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v))) = U at hUo hUc hUk ⊢
  refine ⟨IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_, ?_⟩
  · by_cases h1 : (1 : ℂ) = y
    · have : U.indicator 1 ⁻¹' {y} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ← h1]
      rw [this]; exact hUo
    · by_cases h0 : (0 : ℂ) = y
      · have : U.indicator 1 ⁻¹' {y} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, ← h0]
        rw [this]; exact hUc.isOpen_compl
      · have : U.indicator 1 ⁻¹' {y} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx] <;> assumption
        rw [this]; exact isOpen_empty
  · exact hUk.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal Set.support_indicator_subset hUc)

end GlobalTheory.StdVacuum

open GlobalTheory.AdelicU GlobalTheory.WeilM

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem psi_eq_psiLoc (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (h : At (evFin F v) a) :
    ψ a = psiLoc ψ v (evFin F v a) := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  have h3 : a = GlobalTheory.EmbChart.atPlace v (evFin F v a) := by
    conv_lhs => rw [h1]
    rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
  conv_lhs => rw [h3]
  rfl

theorem acts_indicator {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hψ : ∀ x ∈ v.adicCompletionIntegers F, psiLoc ψ v x = 1)
    (h2 : algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F)
    (w : (κ → AF F) × (κ → AF F))
    (hw : ∀ k, At (evFin F v) (w.1 k) ∧ evFin F v (w.1 k) ∈ v.adicCompletionIntegers F ∧
      At (evFin F v) (w.2 k) ∧ evFin F v (w.2 k) ∈ v.adicCompletionIntegers F)
    (c : AF F) (hc : At (evFin F v) c ∧ evFin F v c ∈ v.adicCompletionIntegers F) :
    Acts (evFin F v) (schr ψ w) (Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1)
      (ψ (⅟(2 : AF F) * c) • Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  have hAt : ∀ {z : AF F}, At (evFin F v) z → ∀ y : AF F, At (evFin F v) (y * z) := fun hz y u hu => by
    have := hz u hu
    rw [smul_eq_mul] at this ⊢
    rw [mul_left_comm, this, mul_zero]
  have hAtAdd : ∀ {z z' : AF F}, At (evFin F v) z → At (evFin F v) z' → At (evFin F v) (z + z') :=
    fun hz hz' u hu => by rw [smul_add, hz u hu, hz' u hu, add_zero]
  have hAtSum : ∀ f : κ → AF F, (∀ i, At (evFin F v) (f i)) → At (evFin F v) (∑ i, f i) :=
    fun f hf u hu => by rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu
  have h2' : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) 2⁻¹ := by
    show evFin F v (algebraMap F (AF F) 2⁻¹) = _
    exact AlgHom.commutes _ _
  have hpsi1 : ∀ z : AF F, At (evFin F v) z → evFin F v z ∈ v.adicCompletionIntegers F → ψ z = 1 :=
    fun z hz hz' => by rw [psi_eq_psiLoc ψ v z hz]; exact hψ _ hz'
  have hcψ : ψ (⅟(2 : AF F) * c) = 1 :=
    hpsi1 _ (hAt hc.1 _) (by rw [map_mul, h2']; exact mul_mem h2 hc.2)
  have hw1 : At (evFin F v) w.1 := fun u hu => funext fun k => by
    have := (hw k).1 u hu
    simpa using this
  intro r hr
  rw [hcψ, one_smul]
  funext x
  simp only [tens, schr]
  rw [hr.1 x w.1 hw1]
  by_cases hx : ∀ k, evFin F v (x k) ∈ v.adicCompletionIntegers F
  · have hx' : (fun i => evFin F v ((x + w.1) i)) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} :=
      fun k => by simp only [Pi.add_apply, map_add]; exact add_mem (hx k) (hw k).2.1
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from hx)]
    have hA : At (evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
      hAtAdd (hAtSum _ fun i => hAt (hw i).2.2.1 _) (hAt (hAtSum _ fun i => hAt (hw i).2.2.1 _) _)
    have hI : evFin F v (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ∈ v.adicCompletionIntegers F := by
      simp only [dotProduct, map_add, map_mul, map_sum, h2']
      exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw i).2.2.2)
        (mul_mem h2 (sum_mem fun i _ => mul_mem (hw i).2.1 (hw i).2.2.2))
    rw [hpsi1 _ hA hI, one_mul]
    simp
  · have hx' : (fun i => evFin F v ((x + w.1) i)) ∉ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} := by
      intro h
      apply hx
      intro k
      have := sub_mem (h k) (hw k).2.1
      simpa using this
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉
      {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from hx)]
    simp

end GlobalTheory.StdVacuum

namespace GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isVac_of_good {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1)
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F)
    (hyz : ∀ x, M.co.e (incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k)))
    (hgen : latAtV X Y v ≤ AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧
      evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = a • incM F t})
    (hψ : ∀ x ∈ v.adicCompletionIntegers F, psiLoc ψ v x = 1)
    (h2 : algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F)
    (hc : ∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F)
    (hs : ∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J t t') ∈ v.adicCompletionIntegers F) :
    M.IsVac ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  refine ⟨indicator_mem_SB v, fun h => ?_, θ, hθ, fun γ hγ => ?_⟩
  · have := congrFun h 0
    simp [Set.indicator, zero_mem] at this
  · obtain ⟨h1, h3⟩ := GlobalTheory.T.coords_and_symplectic_integral_on_placeLattice σ X.J Y.J (θ : E) v M.co.e.toLinearMap T₀ yf zf hyz hc hs γ (hgen hγ)
    exact acts_indicator ψ v hψ h2 (M.co.e γ) h1 _ h3

end GlobalTheory.StdVacuum

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.StdVacuum.eventually_isVac_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ᶠ v in Filter.cofinite, M.IsVac B.ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY M hrat
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm
    (by haveI := hB.unram; infer_instance)
  choose yf zf hyz using hrat
  obtain ⟨sX, hsX⟩ := hX.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hY.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin n → E) →ₗ[ℤ] (Fin d → E) →ₗ[ℤ] Matrix (Fin n) (Fin d) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  set T₀ : Set (Matrix (Fin n) (Fin d) E) := Set.image2 (fun x y => f x y) (sX : Set _) (sY : Set _) with hT₀def
  have hT₀ : T₀.Finite := sX.finite_toSet.image2 _ sY.finite_toSet
  have hmem : ∀ x ∈ X.L, ∀ y ∈ Y.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ T₀ := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin n → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin d → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rwa [Submodule.map₂_span_span] at this
  have hgen : ∀ v : HeightOneSpectrum (𝓞 F), latAtV X Y v ≤ AddSubgroup.closure {z | ∃ a : AF F,
      At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = a • incM F t} := by
    intro v
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hav, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ a).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure T₀ := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure T₀).map g := AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨a, ha, hav, t, ht, rfl⟩
  have hV : ∀ᶠ v in Filter.cofinite, (∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F, psiLoc B.ψ v x = 1) ∧
      algebraMap F (Fv F v) 2⁻¹ ∈ v.adicCompletionIntegers F ∧
      (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
        algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) ∧
      ∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J t t') ∈ v.adicCompletionIntegers F := by
    have hint : ∀ a : F, ∀ᶠ v in Filter.cofinite,
        algebraMap F (Fv F v) a ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
      fun a => (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).2
    refine (GlobalTheory.T.localAddCharComponent_trivial_integers_eventually B.ψ hB.std.1).and ((hint _).and (((Filter.eventually_all_finite hT₀).2
      fun t _ => Filter.eventually_all.2 fun k => (hint _).and (hint _)).and ?_))
    exact (Filter.eventually_all_finite hT₀).2 fun t _ => (Filter.eventually_all_finite hT₀).2 fun t' _ => hint _
  filter_upwards [hV] with v hv
  exact GlobalTheory.StdVacuum.isVac_of_good M B.ψ v θ hθ T₀ yf zf hyz (hgen v) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem uniform_majorant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : κ → AdeleRing (𝓞 F) F),
      ∃ u : (κ → F) → ℝ, Summable u ∧
        ∑' ξ, u ξ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f ∧
        ∀ ξ : κ → F, ‖pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a)‖ ≤ u ξ := by
  obtain ⟨KA, hKA, hcov⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  set Kκ : Set (κ → AdeleRing (𝓞 F) F) := Set.univ.pi fun _ => KA
  have hKκ : IsCompact Kκ := isCompact_univ_pi fun _ => hKA
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R, hR⟩ := hKκ.exists_bound_of_continuousOn (continuous_archV F (κ := κ)).continuousOn
  have hR0 : ∀ b ∈ Kκ, ‖archV F b‖ ≤ max R 0 := fun b hb => (hR b hb).trans (le_max_left _ _)
  set R' := max R 0
  set Kf : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - finV F p.2) '' (tsupport g ×ˢ Kκ)
  have hKf : IsCompact Kf := (hg.2.isCompact.prod hKκ).image (continuous_fst.sub ((continuous_finV F).comp continuous_snd))
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hKf
  haveI := discreteTopology_denomLattice F κ hN
  set k := Module.finrank ℤ (denomLattice F κ N) + 1
  set S : Set (κ → F) := {η | (fun i => mixedEmbedding F (η i)) ∈ denomLattice F κ N}
  have hw : Summable (S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹) := by
    rw [← summable_subtype_iff_indicator]
    let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hs := (summable_one_add_norm_inv (denomLattice F κ N) (k := k) (Nat.lt_succ_self _)).comp_injective hj
    refine hs.congr fun η => ?_
    simp only [Function.comp_apply, j, Submodule.coe_norm]
  set w : (κ → F) → ℝ := S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹ with hwdef
  have hw0 : ∀ η, 0 ≤ w η := fun η => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (by positivity)) η
  refine ⟨k, B * (1 + R') ^ k * 2 ^ k * ∑' η, w η, by
    have h1 : 0 ≤ ∑' η, w η := tsum_nonneg hw0
    have h2 : 0 ≤ R' := le_max_right _ _
    positivity, fun f a => ?_⟩
  set C := (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  choose y hy using fun i => hcov (a i)
  set b : κ → AdeleRing (𝓞 F) F := fun i => a i - algebraMap F (AdeleRing (𝓞 F) F) (y i)
  have hb : b ∈ Kκ := fun i _ => hy i
  have hab : ∀ ξ : κ → F, (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a =
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((ξ + y) i)) + b := by
    intro ξ; funext i; simp [b, map_add]
  refine ⟨fun ξ => B * ((1 + R') ^ k * (2 ^ k * C)) * w (ξ + y), ?_, ?_, fun ξ => ?_⟩
  · exact ((Equiv.addRight y).summable_iff.2 hw).mul_left _
  · have e : ∑' x, w (x + y) = ∑' η, w η := (Equiv.addRight y).tsum_eq w
    rw [tsum_mul_left, e]
    apply le_of_eq; ring
  · beta_reduce
    rw [hab, pureA_eq, archV_add, finV_add, archV_alg, finV_alg, norm_mul]
    by_cases hξ : ξ + y ∈ S
    · have h1 := schwartz_shift_le f k (fun i => mixedEmbedding F ((ξ + y) i)) (archV F b) (hR0 b hb)
      have e : w (ξ + y) = ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹ := by rw [hwdef, Set.indicator_of_mem hξ]
      rw [e]
      calc _ ≤ ((1 + R') ^ k * (2 ^ k * C) * ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = _ := by ring
    · have hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) + finV F b) = 0 := by
        by_contra h0
        apply hξ
        have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) ∈ Kf :=
          ⟨(_, b), ⟨subset_tsupport _ h0, hb⟩, by simp⟩
        refine fun i => ?_
        obtain ⟨z, hz⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * (ξ + y) i)
          fun v => by
            rw [map_mul, map_natCast]
            exact hKN _ hmem i v
        refine ⟨z, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hz
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      rw [hg0, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hB0 (by have : 0 ≤ R' := le_max_right _ _; positivity)) (hw0 _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_pure_le (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)),
      ‖thetaSum F (schr ψ p (pureA F f g))‖ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  obtain ⟨k, c, hc, h⟩ := uniform_majorant F hg
  refine ⟨k, c, hc, fun f p => ?_⟩
  obtain ⟨u, hu, hsum, hb⟩ := h f p.1
  refine (tsum_of_norm_bounded hu.hasSum fun ξ => ?_).trans hsum
  simp only [schr]
  rw [norm_mul, hψ, one_mul]
  exact hb ξ

theorem thetaSum_schA_bdd (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ C : ℝ, ∀ p, ‖thetaSum F (schr ψ p Φ)‖ ≤ C := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨k, c, -, hb⟩ := thetaSum_pure_le F ψ hψ hg
    exact ⟨_, fun p => hb f p⟩
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have e : schr ψ p (0 : (κ → AdeleRing (𝓞 F) F) → ℂ) = 0 := funext fun x => by simp [schr]
    simp [e, thetaSum]
  | add Φ Ψ hΦ hΨ h1 h2 =>
    obtain ⟨C1, hC1⟩ := h1
    obtain ⟨C2, hC2⟩ := h2
    refine ⟨C1 + C2, fun p => ?_⟩
    have e : schr ψ p (Φ + Ψ) = schr ψ p Φ + schr ψ p Ψ := funext fun x => by simp [schr, mul_add]
    have e2 : thetaSum F (schr ψ p (Φ + Ψ)) = thetaSum F (schr ψ p Φ) + thetaSum F (schr ψ p Ψ) := by
      rw [e]
      exact ((schA_cont F ψ hψc hψ hΦ).1 p).tsum_add ((schA_cont F ψ hψc hψ hΨ).1 p)
    rw [e2]
    exact (norm_add_le _ _).trans (add_le_add (hC1 p) (hC2 p))
  | smul a Φ _ h =>
    obtain ⟨C, hC⟩ := h
    refine ⟨‖a‖ * C, fun p => ?_⟩
    have e : schr ψ p (a • Φ) = a • schr ψ p Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, thetaSum_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont GlobalTheory.WeilSchrodinger
open scoped Classical

theorem exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin : ν 𝓕 < ⊤ :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)

end GlobalTheory.LagrThetaAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_representation_compact_character_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  first | exact @GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | exact GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | (intros; apply GlobalTheory.CompactCharDual.exists_dotProduct_eq_local <;> assumption)
end

