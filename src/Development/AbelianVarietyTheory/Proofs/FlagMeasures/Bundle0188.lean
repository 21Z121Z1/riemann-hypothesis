import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.ReImLattice

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_prod (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : Submodule ℤ E)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L'] :
    ZLattice.covolume (L.prod L') (μ.prod μ) = ZLattice.covolume L μ * ZLattice.covolume L' μ := by
  have hD : IsAddFundamentalDomain (L.prod L') (latticeDomain L ×ˢ latticeDomain L')
      (μ.prod μ) := by
    refine IsAddFundamentalDomain.mk' ((measurableSet_latticeDomain L).prod
      (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L x.1
    obtain ⟨a', ha', hu'⟩ := existsUnique_add_mem_latticeDomain L' x.2
    refine ⟨⟨(a, a'), a.2, a'.2⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · simpa [Submodule.vadd_def, add_comm] using ha'
    · rintro ⟨b, hb⟩ hb'
      have h1 := hu ⟨b.1, hb.1⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.1)
      have h2 := hu' ⟨b.2, hb.2⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.2)
      apply Subtype.ext
      simp [← h1, ← h2]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD, measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L' μ)]

theorem reflection_stable (μ : Measure E) [μ.IsAddHaarMeasure] (M : Submodule ℤ (E × E))
    [DiscreteTopology M] [IsZLattice ℝ M] (hM : ∀ p ∈ M, (p.1, -p.2) ∈ M) (A B : Submodule ℤ E)
    (hA : ∀ y, y ∈ A ↔ (y, (0 : E)) ∈ M) (hB : ∀ y, y ∈ B ↔ ((0 : E), y) ∈ M) :
    (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧
      ZLattice.covolume A μ * ZLattice.covolume B μ ≤
        2 ^ Module.finrank ℝ E * ZLattice.covolume M (μ.prod μ) := by
  have h2A : ∀ p ∈ M, p.1 + p.1 ∈ A := fun p hp => by
    rw [hA]
    have := M.add_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  have h2B : ∀ p ∈ M, p.2 + p.2 ∈ B := fun p hp => by
    rw [hB]
    have := M.sub_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  haveI dA : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : A => (⟨(x.1, 0), (hA _).1 x.2⟩ : M))
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.1) h))
  haveI dB : DiscreteTopology B :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : B => (⟨(0, x.1), (hB _).1 x.2⟩ : M))
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.2) h))
  have key : ∀ (C : Submodule ℤ E) (f : E × E →ₗ[ℝ] E), Function.Surjective f →
      (∀ p ∈ M, f p + f p ∈ C) → Submodule.span ℝ (C : Set E) = ⊤ := by
    intro C f hf hC
    rw [eq_top_iff, ← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map,
      ← IsZLattice.span_top (K := ℝ) (L := M), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h := (Submodule.span ℝ (C : Set E)).smul_mem (2⁻¹ : ℝ) (Submodule.subset_span (hC p hp))
    rwa [← two_smul ℝ, inv_smul_smul₀ two_ne_zero] at h
  haveI lA : IsZLattice ℝ A := ⟨key A (LinearMap.fst ℝ E E) LinearMap.fst_surjective h2A⟩
  haveI lB : IsZLattice ℝ B := ⟨key B (LinearMap.snd ℝ E E) LinearMap.snd_surjective h2B⟩
  refine ⟨⟨dA, lA⟩, ⟨dB, lB⟩, ?_⟩
  have hle : A.prod B ≤ M := fun p hp => by
    have := M.add_mem ((hA _).1 hp.1) ((hB _).1 hp.2)
    simpa using this
  rw [← covolume_prod μ A B, covolume_eq_relIndex_mul_of_haar (μ.prod μ) _ M hle]
  refine mul_le_mul_of_nonneg_right ?_ (ZLattice.covolume_pos M (μ.prod μ)).le
  let f : M.toAddSubgroup →+ A :=
    { toFun := fun p => ⟨p.1.1 + p.1.1, h2A _ p.2⟩
      map_zero' := by ext; simp
      map_add' := fun p q => by ext; simp; abel }
  have hK : (nsmulAddMonoidHom (α := A) 2).range.index = 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.index_range_nsmul, ZLattice.rank ℝ A]
  have hc : (A.prod B).toAddSubgroup.addSubgroupOf M.toAddSubgroup =
      (nsmulAddMonoidHom (α := A) 2).range.comap f := by
    ext p
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_prod,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨⟨_, h1⟩, Subtype.ext (by simp [f, two_nsmul])⟩
    · rintro ⟨y, hy⟩
      have h1 : y.1 + y.1 = p.1.1 + p.1.1 := by
        have := congrArg Subtype.val hy
        simpa [f, two_nsmul] using this
      have h2 : y.1 = p.1.1 := by
        rw [← two_smul ℝ, ← two_smul ℝ] at h1
        exact smul_right_injective E two_ne_zero h1
      have h3 : p.1.1 ∈ A := h2 ▸ y.2
      refine ⟨h3, (hB _).2 ?_⟩
      have := M.sub_mem p.2 ((hA _).1 h3)
      convert this using 1
      ext <;> simp
  have hidx : (A.prod B).toAddSubgroup.relIndex M.toAddSubgroup ≤ 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap, ← hK, ← AddSubgroup.relIndex_top_right]
    refine AddSubgroup.relIndex_le_of_le_right le_top ?_
    rw [AddSubgroup.relIndex_top_right, hK]
    positivity
  exact_mod_cast hidx

end General

noncomputable def reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    ((ι → κ → ℝ) × (ι → κ → ℝ)) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v i => ⟨p.1 v i, p.2 v i⟩
      invFun := fun z => (fun v i => (z v i).re, fun v i => (z v i).im)
      map_add' := fun p q => by ext v i; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v i; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }

theorem reImEquiv_apply {ι κ : Type} [Fintype ι] [Fintype κ] (p : (ι → κ → ℝ) × (ι → κ → ℝ))
    (v : ι) (i : κ) : reImEquiv ι κ p v i = ⟨p.1 v i, p.2 v i⟩ := rfl

theorem measurePreserving_reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (reImEquiv ι κ) (Measure.prod volume volume) volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow (κ → ℝ) (κ → ℝ) ι).symm
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ).symm
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := volume_preserving_pi (ι := κ) (fun _ => h3)
  have h5 := volume_preserving_pi (ι := ι) (fun _ => h4.comp h2)
  exact h5.comp h1

theorem real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  intro ι κ _ _ L _ _ hL A B hA hB
  have hmem : ∀ p, p ∈ ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap ↔ reImEquiv ι κ p ∈ L :=
    fun p => Iff.rfl
  have h := reflection_stable volume (ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap)
    (fun p hp => by
      rw [hmem] at hp ⊢
      convert hL _ hp using 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply]) A B
    (fun y => by
      rw [hA, hmem]
      congr! 1)
    (fun y => by
      rw [hB, hmem]
      congr! 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply])
  haveI : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : ((volume : Measure (ι → κ → ℝ)).prod (volume : Measure (ι → κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [ZLattice.covolume_comap L volume _ (measurePreserving_reImEquiv ι κ)] at h
  have hr : Module.finrank ℝ (ι → κ → ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Module.finrank_pi_fintype]; simp
  rwa [hr] at h

end GlobalTheory.ReImLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinates
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.CovPi

open GlobalTheory.HomCovolume

theorem hasCov_pi {β : Type} [Fintype β] {V : β → Type} [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [∀ b, FiniteDimensional ℝ (V b)] [∀ b, MeasurableSpace (V b)]
    [∀ b, BorelSpace (V b)] {μ : ∀ b, Measure (V b)} [∀ b, (μ b).IsAddHaarMeasure]
    {L : ∀ b, Submodule ℤ (V b)} {c : β → ℝ} (h : ∀ i, HasCov (μ i) (L i) (c i)) :
    HasCov (Measure.pi μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  classical
  have hd : ∀ i, DiscreteTopology (L i) := fun i => (h i).1
  have hz : ∀ i, IsZLattice ℝ (L i) := fun i => (h i).2.1
  have hc : ∀ i, ZLattice.covolume (L i) (μ i) = c i := fun i => (h i).2.2
  let B : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℝ (V i) := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis ℝ
  have hBmem : ∀ i j, B i j ∈ L i := fun i j => by
    simp only [B, Module.Basis.ofZLatticeBasis_apply]
    exact (Module.Free.chooseBasis ℤ (L i) j).2
  have hBspan : ∀ i, Submodule.span ℤ (Set.range (B i)) = L i := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis_span ℝ
  have hspan : Submodule.pi Set.univ L = Submodule.span ℤ (Set.range (Pi.basis B)) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_pi] at hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hxi : x i ∈ Submodule.span ℤ (Set.range (B i)) := by
        rw [hBspan]; exact hx i (Set.mem_univ i)
      refine Submodule.span_induction
        (p := fun y _ => Pi.single i y ∈ Submodule.span ℤ (Set.range (Pi.basis B))) ?_ ?_ ?_ ?_ hxi
      · rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨⟨i, j⟩, by simp⟩
      · simp
      · intro y z _ _ hy hz
        rw [Pi.single_add]; exact add_mem hy hz
      · intro a y _ hy
        rw [Pi.single_smul]; exact Submodule.smul_mem _ a hy
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_pi]
      intro i' _
      rw [Pi.basis_apply]
      by_cases hi : i' = i
      · subst hi; simpa using hBmem i' j
      · simp [hi]
  rw [hspan]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (Pi.basis B) _)]
  have hfd : ZSpan.fundamentalDomain (Pi.basis B) = Set.univ.pi fun i => ZSpan.fundamentalDomain (B i) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall]
  rw [hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hc i, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (L i)) (μ i)), measureReal_def]

theorem measurePreserving_of_sum_sq {κ σ : Type} [Fintype κ] [Fintype σ]
    (e : (κ → ℂ) ≃L[ℝ] (σ → ℂ)) (he : ∀ z, ∑ j, ‖e z j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    MeasurePreserving e volume volume := by
  let T : EuclideanSpace ℂ κ ≃L[ℝ] (κ → ℂ) := ((EuclideanSpace.equiv κ ℂ).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hnorm : ∀ v : EuclideanSpace ℂ κ, ‖v‖ ^ 2 = ∑ i, ‖T v i‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hT : MeasurePreserving T volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ κ T hnorm
  have hTe : MeasurePreserving (T.trans e) volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ σ (T.trans e) fun v => by
      rw [hnorm v, ContinuousLinearEquiv.trans_apply, he]
  have hTs := MeasurePreserving.symm T.toHomeomorph.toMeasurableEquiv hT
  have hfun : (⇑e) = (T.trans e) ∘ T.toHomeomorph.toMeasurableEquiv.symm := by
    funext z
    simp
  rw [hfun]
  exact hTe.comp hTs

private theorem measurePreserving_piCurry_complex {I : Type} [Fintype I] {K : I → Type} [∀ i, Fintype (K i)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
  symm
  show Measure.pi (fun i : I => Measure.pi fun _ : K i => (volume : Measure ℂ)) = _
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ fun _ : K i => {s : Set ℂ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℂ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  obtain rfl : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) ⁻¹'
      Set.univ.pi (fun i => Set.univ.pi (t i)) = Set.univ.pi fun p : (Σ i, K i) => t p.1 p.2 := by
    ext f
    simp [MeasurableEquiv.coe_piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  simp only [Measure.pi_pi]

attribute [local instance] haar_two haar_three

theorem covolume_pi_unitary : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  intro ι κ β _ _ _ r s Φ hΦ M hM L hL
  classical
  let Ψ : (ι → κ → ℂ) ≃ₗ[ℂ] (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun z b v => Φ v (z v) b
      invFun := fun w v => (Φ v).symm fun b => w b v
      map_add' := fun x y => by funext b v; simp
      map_smul' := fun c x => by funext b v; simp
      left_inv := fun z => by funext v; simp
      right_inv := fun w => by funext b v; simp }
  let F : ((Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)) → ℂ) ≃ₗ[ℂ]
      (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun w b v p q => w ⟨b, v, p, q⟩
      invFun := fun u x => u x.1 x.2.1 x.2.2.1 x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := LinearEquiv.piCurry ℂ fun (_ : ι) (_ : κ) => ℂ
  let E := G.trans (Ψ.trans F.symm)
  have hE : MeasurePreserving (E.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    apply measurePreserving_of_sum_sq
    intro z
    have hz : ∀ j : (Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)),
        (E.restrictScalars ℝ).toContinuousLinearEquiv z j =
          Φ j.2.1 (fun k => z ⟨j.2.1, k⟩) j.1 j.2.2.1 j.2.2.2 := fun j => rfl
    simp only [hz, Fintype.sum_sigma]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => hΦ v _
  have hG : MeasurePreserving (MeasurableEquiv.piCurry fun (_ : ι) (_ : κ) => ℂ) volume volume :=
    measurePreserving_piCurry_complex
  have hF : MeasurePreserving F volume volume := by
    have h := (volume_preserving_pi fun b => volume_preserving_pi fun (_ : ι) =>
        measurePreserving_piCurry_complex (I := Fin (r b)) (K := fun _ => Fin (s b))).comp
      ((volume_preserving_pi fun b =>
        measurePreserving_piCurry_complex (I := ι) (K := fun _ => Σ _ : Fin (r b), Fin (s b))).comp
        (measurePreserving_piCurry_complex (I := β) (K := fun b => Σ _ : ι, Σ _ : Fin (r b), Fin (s b))))
    exact h
  have hΨ : MeasurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    have h := hF.comp (hE.comp (MeasurePreserving.symm _ hG))
    convert h using 1
    funext z
    rfl
  have := haar_two ι κ
  have hB3 : ∀ b, (volume : Measure (ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure :=
    fun b => haar_three ι _ _
  have : (volume : Measure (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure := by
    rw [← hΨ.map_eq]; infer_instance
  show HasCov volume L _
  refine HasCov.of_measurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv hΨ
    (L' := Submodule.pi Set.univ M) ?_ ?_
  · intro z
    rw [hL, Submodule.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact Iff.rfl
  · exact hasCov_pi (μ := fun _ => volume) fun b => by
      obtain ⟨hd, hz⟩ := hM b
      exact ⟨hd, hz, rfl⟩

end GlobalTheory.CovPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetRealSandwich
section
namespace GlobalTheory.DeterminantRealSandwich

open Matrix

noncomputable def rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  LinearMap.pi fun a => Matrix.toLin' C ∘ₗ LinearMap.proj a

theorem det_rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (rowAct C) = C.det ^ j := by
  unfold rowAct
  rw [LinearMap.det_pi (fun _ : Fin j => Matrix.toLin' C)]
  simp [LinearMap.det_toLin']

def swapIdx (j : ℕ) : (Fin j → Fin j → ℂ) ≃ₗ[ℂ] (Fin j → Fin j → ℂ) where
  toFun h := fun a b => h b a
  invFun h := fun a b => h b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  rowAct Bᵀ ∘ₗ ((swapIdx j).toLinearMap ∘ₗ rowAct A ∘ₗ (swapIdx j).symm.toLinearMap)

theorem det_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (sandwich A B) = B.det ^ j * A.det ^ j := by
  unfold sandwich
  rw [LinearMap.det_comp, LinearMap.det_conj, det_rowAct, det_rowAct, Matrix.det_transpose]

theorem sandwich_apply {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) (h : Fin j → Fin j → ℂ)
    (a b : Fin j) : sandwich A B h a b = (A * Matrix.of h * B) a b := by
  simp [sandwich, rowAct, swapIdx, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_real_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det ((sandwich A B).restrictScalars ℝ) = (‖A.det‖ ^ 2 * ‖B.det‖ ^ 2) ^ j := by
  rw [LinearMap.det_restrictScalars, det_sandwich, Algebra.norm_complex_apply, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, mul_pow, mul_comm]

theorem det_real_family (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] ι → Fin j → Fin j → ℂ)
    (hL : ∀ (h : ι → Fin j → Fin j → ℂ) (w : ι),
      Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w : ι, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  have e : L = LinearMap.pi fun w =>
      ((sandwich (A w) (B w)).restrictScalars ℝ) ∘ₗ LinearMap.proj w := by
    refine LinearMap.ext fun h => funext fun w => funext fun a => funext fun b => ?_
    have h1 : L h w a b = (A w * Matrix.of (h w) * B w) a b := by
      rw [← hL h w]; rfl
    rw [h1, ← sandwich_apply]
    rfl
  rw [e, LinearMap.det_pi (fun w => (sandwich (A w) (B w)).restrictScalars ℝ)]
  exact Finset.prod_congr rfl fun w _ => det_real_sandwich _ _

end GlobalTheory.DeterminantRealSandwich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.PhMajProof

theorem local_integrable (n : ℕ) (ε : Fin n → Bool) (h s : ℝ) (hs : 0 ≤ s)
    (hyp : rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) :
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  rcases hyp with h0 | hlt
  · have key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) =
        fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      funext g
      rw [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]
      simp [decE]
    rw [key]
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)
  · have hh : 0 ≤ h := by
      have : 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) :=
        mul_nonneg (by positivity) (add_nonneg hs (by positivity))
      linarith
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)

theorem phMaj : PhMaj := by
  intro B d h hds hloc
  have hd : ∀ v, 0 < d v := fun v => (hds v).2.2.2.1
  have hdp : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).le
  have hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) := by
    intro v
    have hon := (hds v).2.1.2.2.1.2.2 (B.w v)
    refine hon.comp_continuous ?_ ?_
    · unfold uMat
      exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    · intro g
      exact (g v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold ph
    exact continuous_const.mul (continuous_star.comp
      (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))
  · intro g
    unfold ph majPh
    rw [norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp
  · intro s hs hyp
    have key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf =>
        (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v)))) := by
      funext g
      unfold majPh dSum
      rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [key]
    unfold muInf
    have hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v,
        (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v)))))
        (Measure.pi fun v => muG (B.I.ε v)) :=
      Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)
    exact hprod.const_mul _

end GlobalTheory.Dec.PhMajProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstance
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.Place

theorem comap_mk_phi (I : AutInst) (v : InfinitePlace I.F) :
    (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E) = v := by
  have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem placeMatch : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  intro I xf
  have hb := GlobalTheory.Count.FrameMajorant.comap_bijective I
  refine ⟨⟨fun v v' h => ?_, fun w => ⟨w.comap (algebraMap I.F I.E), hb.1 (comap_mk_phi I _)⟩⟩, fun v => ?_⟩
  · have h' : InfinitePlace.mk (I.φ v) = InfinitePlace.mk (I.φ v') := h
    rw [← comap_mk_phi I v, h', comap_mk_phi]
  · have he := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk (I.φ v))
    have hu : ∀ u, uMat ((((1, xf) : I.GA)).1 u) = 1 := fun u => rfl
    rw [comap_mk_phi] at he
    unfold frm
    rw [comap_mk_phi, hu, Matrix.mul_one]
    by_cases h : (InfinitePlace.mk (I.φ v)).embedding = I.φ v
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨he.resolve_left h, if_neg h⟩

end GlobalTheory.RadCov.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinatesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_lie_coordinates : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, A (c + 1) ≤ A c) → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) → ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧ ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  first | exact @GlobalTheory.NilCovSec.exists_continuous_section | exact GlobalTheory.NilCovSec.exists_continuous_section | (intros; apply GlobalTheory.NilCovSec.exists_continuous_section <;> assumption)
end

