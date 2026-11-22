import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0826
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0797
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0829
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0825
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBaseChangeSq
section
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MdBase

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange MeasureTheory.Measure
open scoped ENNReal NNReal NumberField.AdeleRing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem map_smul_pi (n : ℕ) (a : IdeleGroup K) :
    (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      (Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹) ^ n •
        Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
  have hsm : Measurable fun y : 𝔸[K] ↦ a • y := (Homeomorph.smul a).continuous.measurable
  have hmeas : Measurable fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i :=
    measurable_pi_lambda _ fun i ↦ hsm.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ with hcdef
  have hmap : (adeleMeasure K).map (fun y ↦ a • y) = c • adeleMeasure K := by
    rw [map_smul_adeleMeasure]
    rfl
  have h1 : (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      Measure.pi fun _ : Fin n ↦ c • adeleMeasure K := by
    refine (pi_eq fun s hs ↦ ?_).symm
    rw [map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i ↦ (fun y ↦ a • y) ⁻¹' s i := by
      ext x
      simp
    rw [hpre, pi_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← hmap, map_apply hsm (hs i)]
  have h2 : (Measure.pi fun _ : Fin n ↦ c • adeleMeasure K) =
      c ^ n • Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
    refine pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.coe_pow]
  rw [h1, h2]

theorem ideleModule_ideleEmbedding (x : IdeleGroup K) :
    (IdeleGroup.ideleModule L (ideleEmbedding K L x) : ℝ) =
      (IdeleGroup.ideleModule K x : ℝ) ^ Module.finrank K L := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  set n := Module.finrank K L with hn
  let e : 𝔸[L] ≃ₗ[𝔸[K]] (Fin n → 𝔸[K]) := (adeleBasis (Module.finBasis K L)).equivFun
  have hce : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hcs : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : 𝔸[L] ≃ₜ (Fin n → 𝔸[K]) :=
    { toEquiv := e.toEquiv, continuous_toFun := hce, continuous_invFun := hcs }
  set μ : Measure (Fin n → 𝔸[K]) := Measure.pi fun _ ↦ adeleMeasure K with hμ
  set ν : Measure 𝔸[L] := μ.map e.symm with hν
  have hms : Measurable e.symm := hcs.measurable
  haveI : ν.IsAddHaarMeasure :=
    isAddHaarMeasure_map _ e.symm.toLinearMap.toAddMonoidHom hcs e.symm.surjective
      h.symm.isClosedEmbedding.tendsto_cocompact
  set X := ideleEmbedding K L x with hX
  have hcomp : (fun y : 𝔸[L] ↦ X • y) ∘ e.symm = e.symm ∘ (fun v i ↦ x • v i) := by
    funext v
    have hv : (fun i ↦ x • v i) = (x : 𝔸[K]) • v := by
      funext i
      simp [Units.smul_def]
    simp only [Function.comp_apply]
    rw [hv, map_smul, Units.smul_def]
    change (X : 𝔸[L]) * e.symm v = (x : 𝔸[K]) • e.symm v
    rw [Algebra.smul_def (x : 𝔸[K]), algebraMap_adeleRing]
    rfl
  have hsmL : Measurable fun y : 𝔸[L] ↦ X • y := (Homeomorph.smul X).continuous.measurable
  have hsmK : Measurable fun v : Fin n → 𝔸[K] ↦ fun i ↦ x • v i :=
    measurable_pi_lambda _ fun i ↦
      (Homeomorph.smul x).continuous.measurable.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K x : ℝ))⁻¹ with hcdef
  have h1 : ν.map (fun y ↦ X • y) = c ^ n • ν := by
    rw [hν, Measure.map_map hsmL hms, hcomp, ← Measure.map_map hms hsmK, hμ, map_smul_pi,
      Measure.map_smul]
  have hc := isAddLeftInvariant_eq_smul ν (adeleMeasure L)
  set C := ν.addHaarScalarFactor (adeleMeasure L)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hc, ENNReal.coe_eq_zero.1 h0, zero_smul]
    exact (NeZero.ne ν) this
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : 𝔸[L])
  have hpos : adeleMeasure L S ≠ 0 := (measure_pos_of_mem_nhds _ hS0).ne'
  have htop : adeleMeasure L S ≠ ⊤ := hS.measure_lt_top.ne
  rw [hc, Measure.map_smul, map_smul_adeleMeasure] at h1
  have h2 := congrArg (fun m : Measure 𝔸[L] ↦ m S) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  rw [mul_left_comm] at h2
  have hne : (C : ℝ≥0∞) * adeleMeasure L S ≠ 0 := mul_ne_zero hC0 hpos
  have hnt : (C : ℝ≥0∞) * adeleMeasure L S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top htop
  have h3 := (ENNReal.mul_left_inj hne hnt).1 h2
  have hK0 : (0 : ℝ) ≤ (IdeleGroup.ideleModule K x : ℝ)⁻¹ :=
    inv_nonneg.2 (IdeleGroup.ideleModule K x).2.le
  have h4 : ((c ^ n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (((IdeleGroup.ideleModule K x : ℝ))⁻¹ ^ n) := by
    rw [ENNReal.ofReal_pow hK0, ENNReal.coe_pow]
    rfl
  rw [h4] at h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule L X).2.le)
    (pow_nonneg hK0 n)).1 h3
  rw [inv_pow] at h5
  exact inv_inj.1 h5

end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
  PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem ideleModule_ideleEquiv_ofF : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  intro F E _ _ _ _ _ σ hcm a
  have he : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a) = ideleEmbedding F E a :=
    Units.ext (GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (a : AF F))
  rw [he, ideleModule_ideleEmbedding, hcm.2.2.1]
  rfl

end

end GlobalTheory.CompanionTheory.SW.MdBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IdeleModBdd

theorem ideleModule_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  intro K _ _ C hC
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (AdeleRing (𝓞 K) K) := fun S =>
    {x | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers K}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ S)).preimage continuous_snd
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ x.2 v ∈ v.adicCompletionIntegers K}.Finite :=
      Filter.eventually_cofinite.1 x.2.2
    exact Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)⟩
  have hdir : Directed (· ⊆ ·) U := fun S T =>
    ⟨S ∪ T, fun x hx v hv => hx v fun h => hv (Finset.mem_union_left _ h),
      fun x hx v hv => hx v fun h => hv (Finset.mem_union_right _ h)⟩
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  have hfinB : ∀ v : HeightOneSpectrum (𝓞 K), ∃ B : ℝ, ∀ x ∈ C, ‖x.2 v‖ ≤ B := fun v => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.2 v‖ :=
      continuous_norm.comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  have hinfB : ∀ w : InfinitePlace K, ∃ B : ℝ, ∀ x ∈ C, ‖x.1 w‖ ≤ B := fun w => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.1 w‖ :=
      continuous_norm.comp ((continuous_apply w).comp continuous_fst)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose Bf hBf using hfinB
  choose Bi hBi using hinfB
  refine ⟨(∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult) * ∏ v ∈ S, max (Bf v) 1, ?_⟩
  intro a ha
  rw [IdeleGroup.ideleModule_eq]
  have h1 : ∏ w : InfinitePlace K, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult ≤
      ∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult :=
    Finset.prod_le_prod (fun _ _ => by positivity) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((hBi w _ ha).trans (le_max_left _ _)) _
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤
      ∏ v ∈ S, max (Bf v) 1 := by
    have hfs := IdeleGroup.finite_mulSupport_norm a
    have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        ‖(a : AdeleRing (𝓞 K) K).2 v‖) ⊆ ((hfs.toFinset ∪ S : Finset _) : Set _) := fun v hv => by
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hv
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ hfs.toFinset ∪ S, ‖(a : AdeleRing (𝓞 K) K).2 v‖
        ≤ ∏ v ∈ hfs.toFinset ∪ S, (if v ∈ S then max (Bf v) 1 else 1) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
          split_ifs with hv
          · exact (hBf v _ ha).trans (le_max_left _ _)
          · exact (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 (hS ha v hv))
      _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
          (Finset.prod_subset Finset.subset_union_right fun v _ hv => if_neg hv).symm
      _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
  exact mul_le_mul h1 h2 (IdeleGroup.finiteModule_pos a).le
    (Finset.prod_nonneg fun _ _ => by positivity)

end GlobalTheory.CompanionTheory.IdeleModBdd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct ENNReal NNReal Matrix Classical NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ModConj

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_involution_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he2 : ∀ x, e (e x) = x) (ν : Measure G) [ν.IsAddHaarMeasure] [SecondCountableTopology G] :
    ν.map e = ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]
  have hid : (e ∘ e : G → G) = id := funext he2
  rw [hid, Measure.map_id] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbb : b * b = 1 := by
    have h3 : ((b * b : ℝ≥0) • ν) K = ((1 : ℝ≥0) • ν) K := by rw [← h2, one_smul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  have hb1 : b = 1 := by
    have := (mul_self_eq_one_iff (a := (b : ℝ))).1 (by exact_mod_cast hbb)
    rcases this with h | h
    · exact_mod_cast h
    · have := b.2; simp only [NNReal.val_eq_coe] at this; linarith
  rw [hb, hb1, one_smul]

def conjA (σ : E →ₐ[F] E) : 𝔸[E] →+* 𝔸[E] :=
  (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).toRingEquiv.toRingHom.comp
    ((sigR (AF F) σ).comp (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm.toRingEquiv.toRingHom)

theorem conjA_apply (σ : E →ₐ[F] E) (y : 𝔸[E]) :
    conjA σ y = GroundTheory.BlockD.ThmBHecke.adeleEquiv F E
      (sigR (AF F) σ ((GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm y)) := rfl

theorem sig_sig {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem continuous_sig {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : Continuous (sigR (AF F) σ) :=
  (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.1

theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

def conjE {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : 𝔸[E] ≃ₜ+ 𝔸[E] where
  toFun := conjA σ
  invFun := conjA σ
  left_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  right_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  map_add' := map_add _
  continuous_toFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)
  continuous_invFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)

end

theorem ideleModule_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : (AF F ⊗[F] E)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E
        (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ) =
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) := by
  intro F E _ _ _ _ _ σ hcm x
  letI : MeasurableSpace 𝔸[E] := measurableSpace_adeleRing E
  set a := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x with ha
  set a' := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x) with ha'
  set e := conjE hcm with he
  set ν := adeleMeasure E with hν
  have hinv : ∀ y, e (e y) = y := fun y => e.left_inv y
  have hcoe : ∀ y, e y = conjA σ y := fun _ => rfl
  have hea : e (a : 𝔸[E]) = (a' : 𝔸[E]) := by
    rw [hcoe, conjA_apply, ha, ha', GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv,
      GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, AlgEquiv.symm_apply_apply]
    rfl
  have key : ∀ y : 𝔸[E], a' • y = e (a • e y) := fun y => by
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcoe (_ * _), map_mul, ← hcoe, ← hcoe,
      hinv, hea]
  have hmeas : Measurable e := e.continuous.measurable
  have hm : Measurable (fun y : 𝔸[E] => a • y) := (Homeomorph.smul a).continuous.measurable
  have hνe : ν.map e = ν := map_involution_eq e hinv ν
  have hfun : (fun y : 𝔸[E] => a' • y) = e ∘ (fun y => a • y) ∘ e := funext key
  have h1 : ν.map (fun y : 𝔸[E] => a' • y) =
      ENNReal.ofReal ((IdeleGroup.ideleModule E a : ℝ))⁻¹ • ν := by
    rw [hfun, ← Measure.map_map hmeas (hm.comp hmeas), ← Measure.map_map hm hmeas, hνe, hν,
      map_smul_adeleMeasure, Measure.map_smul, ← hν, hνe]
  have h2 := map_smul_adeleMeasure (K := E) a'
  rw [← hν, h1] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : 𝔸[E])
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have h3 := congrArg (fun m : Measure 𝔸[E] => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule E a).2.le)
    (inv_nonneg.2 (IdeleGroup.ideleModule E a').2.le)).1 h4
  exact (inv_injective h5).symm

end GlobalTheory.CompanionTheory.SW.ModConj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteAdeleHaarScalingTotallyReal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarUnit

theorem norm_inv_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (n : (InfiniteAdeleRing F)ˣ) :
    ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ =
      ((∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ : ℝ≥0) := by
  have hmult : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (hF.isReal w)]
  have hw : ∀ w : InfinitePlace F,
      ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ =
        ‖(n : InfiniteAdeleRing F) w‖⁻¹ := fun w => by
    have h1 : ((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w *
        (n : InfiniteAdeleRing F) w = 1 := congrFun n.inv_mul w
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  rw [InfiniteAdeleRing.norm_def]
  simp only [hmult, pow_one, hw, NNReal.coe_inv, NNReal.coe_prod, coe_nnnorm]
  rw [Finset.prod_inv_distrib]

section Borel

attribute [local instance 100000] GroundTheory.Global.measurableSpace_infiniteAdeleRing

theorem infinite_adele_haar_scaling_by_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    {m : MeasurableSpace (InfiniteAdeleRing F)} (hm : @BorelSpace _ _ m)
    (li : Measure (InfiniteAdeleRing F)) (hli : li.IsAddHaarMeasure)
    (n : (InfiniteAdeleRing F)ˣ) :
    li.map (fun t => (n : InfiniteAdeleRing F) * t) =
      (∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ • li := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul li (infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, map_mul_left_infiniteAdeleMeasure, smul_comm, norm_inv_unit F hF n,
    ENNReal.ofReal_coe_nnreal]
  rfl

end Borel

theorem map_mul_unit : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ n : (Ainf F)ˣ,
      li.map (fun t => (n : Ainf F) * t) =
        (∏ w : InfinitePlace F, ‖(n : Ainf F) w‖₊)⁻¹ • li := by
  intro F _ _ hF li hli n
  exact infinite_adele_haar_scaling_by_unit F hF (m := measAinf) ⟨rfl⟩ li hli n

end GlobalTheory.CompanionTheory.SW.HaarUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormulaStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_formula : Dens := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOne.dens | exact GlobalTheory.CompanionTheory.SW.RankOne.dens | (intros; apply GlobalTheory.CompanionTheory.SW.RankOne.dens <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormulaStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleRayEqPowDegree
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ r hr δ hδ
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hw : ∀ w : InfinitePlace F, ‖(θ δ) w‖ = δ := by
    intro w
    have hreal : w.IsReal := hF.isReal w
    have hu := congrArg (fun f : ℝ →+* ℝ => f δ)
      (Subsingleton.elim ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal).comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) (RingHom.id ℝ))
    have hu' : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal ((θ δ) w) = δ := hu
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero
      (map_zero _) ((θ δ) w)
    rw [hu', Real.norm_eq_abs, abs_of_pos hδ] at hn
    exact hn.symm
  change (∏ w, ‖((r δ : AF F)).1 w‖ ^ w.mult) * (∏ᶠ v, ‖((r δ : AF F)).2 v‖) = δ ^ Module.finrank ℚ F
  rw [h1, h2]
  simp only [hw]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  simp

end GlobalTheory.CompanionTheory.BasePsi

end
end

