import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro hD h𝓕
  have hker : IsClosed ((π.ker : Set P)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  have hsc : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hlc : LocallyCompactSpace π.ker := hker.locallyCompactSpace
  have hσc : SigmaCompactSpace π.ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνσ : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  set e := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with he
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [e.image_eq_preimage_symm]
    exact (hD.nullMeasurableSet.prod h𝓕).preimage
      (MeasurableEquiv.quasiMeasurePreserving_symm (ν.prod μ₁) e.toMeasurableEquiv)
  · intro f hf
    rw [hemb.restrict_map, Set.preimage_image_eq _ e.injective, hemb.lintegral_map,
      ← Measure.prod_restrict, lintegral_prod_symm']
    · rfl
    · exact hf.comp hemb.measurable

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicQuotientMeasure
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem isHaarMeasure_map_splitHomeo :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι ν _ μ₁ _ hconj
  have hclosed : IsClosed (π.ker : Set P) := by
    have hk : (π.ker : Set P) = π ⁻¹' {1} := by
      ext p
      simp
    rw [hk]
    exact isClosed_singleton.preimage hπ
  have : LocallyCompactSpace π.ker := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have : SigmaCompactSpace π.ker := inferInstance
  have : SigmaFinite ν := inferInstance
  set Φ := splitHomeo ι π hι hπ hπι with hΦdef
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hinv : (Measure.map Φ (ν.prod μ₁)).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    set k₀ := kerPart ι π hπι g
    have hcm : Measurable (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) :=
      ((continuous_conj ι π hι).comp (Continuous.prodMk_right (π g))).measurable
    have hfm : Measurable (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) :=
      (measurable_const_mul k₀).comp hcm
    have hhm : Measurable (fun u : G₁ => π g * u) := measurable_const_mul _
    have e1 : Measure.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) ν = ν := by
      have hsplit : (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) =
          (fun x => k₀ * x) ∘ (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) := rfl
      rw [hsplit, ← Measure.map_map (measurable_const_mul k₀) hcm, hconj, map_mul_left_eq_self]
    have e2 : Measure.map (fun u : G₁ => π g * u) μ₁ = μ₁ := map_mul_left_eq_self μ₁ _
    have hcomp : (fun x => g * x) ∘ Φ =
        Φ ∘ Prod.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) (fun u : G₁ => π g * u) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, hΦdef, splitHomeo_apply]
      exact mul_split ι π hπι g z.1 z.2
    rw [Measure.map_map (measurable_const_mul g) hΦm, hcomp, ← Measure.map_map hΦm (hfm.prodMap hhm),
      ← Measure.map_prod_map ν μ₁ hfm hhm, e1, e2]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : P)
  have hKm : MeasurableSet K := hK.measurableSet
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩ ?_ ?_
  · rw [Measure.map_apply hΦm hKm]
    have hopen : IsOpen (Φ ⁻¹' interior K) := isOpen_interior.preimage Φ.continuous
    have hne : (Φ ⁻¹' interior K).Nonempty := by
      obtain ⟨z, hz⟩ := Φ.surjective 1
      refine ⟨z, ?_⟩
      show Φ z ∈ interior K
      rw [hz]
      exact mem_interior_iff_mem_nhds.mpr hK1
    exact ((hopen.measure_pos _ hne).trans_le (measure_mono (Set.preimage_mono interior_subset))).ne'
  · rw [Measure.map_apply hΦm hKm]
    exact (Φ.isCompact_preimage.mpr hK).measure_lt_top.ne

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSigns
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeSign

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ x ∈ s, f x ≠ 0) :
    0 < (-1 : ℝ) ^ (s.filter fun x => f x < 0).card * ∏ x ∈ s, f x := by
  have e : (-1 : ℝ) ^ (s.filter fun x => f x < 0).card
      = ∏ x ∈ s, (if f x < 0 then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite]; simp
  rw [e, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro x hx
  split_ifs with hneg
  · linarith
  · have : 0 < f x := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (h x hx))
    linarith

theorem sign_div {a b P Q : ℝ} (hP : 0 < a * P) (hQ : 0 < b * Q) : 0 < a * b * (P / Q) := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  have e : a * b * (P / Q) = (a * P) * (b * Q) / Q ^ 2 := by
    field_simp
  rw [e]
  exact div_pos (mul_pos hP hQ) (by positivity)

theorem above_eq {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) :
    above d d' r = (univ.filter fun k => r < d k).card + (univ.filter fun j => r < d' j).card := by
  unfold above
  simp only [Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr!

theorem pfSign {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) :
    (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧
      ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  have hd : ∀ {i k}, k ≠ i → d i - d k ≠ 0 := by
    intro i k hk h
    apply hk
    have := hinj (a₁ := Sum.inl k) (a₂ := Sum.inl i) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hd' : ∀ {j k}, k ≠ j → d' j - d' k ≠ 0 := by
    intro j k hk h
    apply hk
    have := hinj (a₁ := Sum.inr k) (a₂ := Sum.inr j) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hx : ∀ i j, d i - d' j ≠ 0 := by
    intro i j h
    have := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using sub_eq_zero.mp h)
    simp at this
  have hy : ∀ j i, d' j - d i ≠ 0 := by
    intro j i h
    exact hx i j (by linarith)
  constructor
  · intro i
    have h1 := sign_prod (univ.erase i) (fun k => d i - d k)
      (fun k hk => hd (Finset.ne_of_mem_erase hk))
    have h2 := sign_prod (univ : Finset (Fin m)) (fun j => d i - d' j) (fun j _ => hx i j)
    have e1 : ((univ.erase i).filter fun k => d i - d k < 0) = univ.filter fun k => d i < d k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    have e2 : (univ.filter fun j => d i - d' j < 0) = univ.filter fun j => d i < d' j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2
  · intro j
    have h1 := sign_prod (univ : Finset (Fin (m + 1))) (fun i => d' j - d i) (fun i _ => hy j i)
    have h2 := sign_prod (univ.erase j) (fun k => d' j - d' k)
      (fun k hk => hd' (Finset.ne_of_mem_erase hk))
    have e1 : (univ.filter fun i => d' j - d i < 0) = univ.filter fun i => d' j < d i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    have e2 : ((univ.erase j).filter fun k => d' j - d' k < 0)
        = univ.filter fun k => d' j < d' k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2

end GlobalTheory.CompanionTheory.RgHeSign
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentity
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe.Frame

open Polynomial

theorem degree_sub_lt_of_nextCoeff_eq {p q : ℝ[X]} {m : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m + 1) (hqd : q.natDegree = m + 1) (hn : p.nextCoeff = q.nextCoeff) :
    (p - q).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub]
  rcases hk.eq_or_lt with rfl | hk'
  · have h1 : p.nextCoeff = p.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hpd]; rfl
    have h2 : q.nextCoeff = q.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hqd]; rfl
    rw [← h1, ← h2, hn, sub_self]
  · rcases (Nat.succ_le_of_lt hk').eq_or_lt with rfl | hk''
    · have h1 := hp.coeff_natDegree
      have h2 := hq.coeff_natDegree
      rw [hpd] at h1
      rw [hqd] at h2
      rw [h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
        sub_zero]

theorem prod_eq_partial_fraction {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hd' : Function.Injective d') :
    (∏ i, (X - C (d i))) = (X - C (pfX d d')) * (∏ j, (X - C (d' j))) +
      ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
  have hPm : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQm : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hRm : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQm
  have hRd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m + 1 := by
    rw [(monic_X_sub_C _).natDegree_mul hQm, hQd, natDegree_X_sub_C]; omega
  have hn : (∏ i, (X - C (d i)) : ℝ[X]).nextCoeff =
      ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).nextCoeff := by
    rw [(monic_X_sub_C _).nextCoeff_mul hQm, prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff,
      nextCoeff_X_sub_C, pfX]
    ring
  have hD := degree_sub_lt_of_nextCoeff_eq hPm hRm hPd hRd hn
  have hS : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < (m : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul]
    have hL : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).natDegree < n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      have hj : (univ.erase j).card + 1 = m := by
        rw [Finset.card_erase_of_mem (mem_univ j)]
        have : 0 < m := j.pos
        simp only [card_univ, Fintype.card_fin]
        omega
      simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hL, mul_zero]
  have hcard : (#(univ : Finset (Fin m)) : ℕ) = m := by simp
  have key := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin m)))
    (v := d') (f := (∏ i, (X - C (d i))) - (X - C (pfX d d')) * ∏ j, (X - C (d' j)))
    (g := ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)))
    hd'.injOn (by rw [hcard]; exact hD) (by rw [hcard]; exact hS) (by
      intro j _
      have hne : ∏ k ∈ univ.erase j, (d' j - d' k) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hk).1 (hd' h).symm
      have hQ0 : (∏ l, (d' j - d' l)) = 0 :=
        Finset.prod_eq_zero (mem_univ j) (sub_self _)
      have hterm : ∀ l ∈ (univ : Finset (Fin m)), l ≠ j →
          pfR d d' l * ∏ k ∈ univ.erase l, (d' j - d' k) = 0 := by
        intro l _ hl
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl.symm, mem_univ j⟩) (sub_self _), mul_zero]
      simp only [eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finset_sum]
      rw [hQ0, mul_zero, sub_zero, Finset.sum_eq_single_of_mem j (mem_univ j) hterm, pfR,
        div_mul_cancel₀ _ hne])
  rw [← key]
  ring

theorem pfZero {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) (i : Fin (m + 1)) :
    d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  have hd' : Function.Injective d' := fun a b h =>
    Sum.inr_injective (hinj (by simpa using h))
  have hne : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h => by
    simpa using hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using h)
  have hQ : ∏ j, (d i - d' j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have h := congrArg (eval (d i)) (prod_eq_partial_fraction d d' hd')
  simp only [eval_add, eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finset_sum] at h
  rw [Finset.prod_eq_zero (mem_univ i) (sub_self _)] at h
  have hsum : ∀ j, pfR d d' j * ∏ k ∈ univ.erase j, (d i - d' k) =
      (pfR d d' j / (d i - d' j)) * ∏ k, (d i - d' k) := by
    intro j
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    field_simp [hne j]
  simp only [hsum, ← Finset.sum_mul] at h
  rw [← add_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hQ

end GlobalTheory.CompanionTheory.RgHe.Frame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A →
    (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧
    (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧
    ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧
      ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := by
  intro p _ A _ h
  have hp : p.Prime := Fact.out
  have hadd : ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h.char]
    simp
  let F : A →+* A :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd }
  have hk : ∀ k : ℕ, Function.Bijective fun x : A => x ^ p ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, pow_one]
      exact Function.bijective_id
    | succ k ih =>
      have : (fun x : A => x ^ p ^ (k + 1)) = (fun x : A => x ^ p) ∘ (fun x : A => x ^ p ^ k) := by
        funext x
        simp only [Function.comp_apply]
        rw [pow_succ, pow_mul]
      rw [this]
      exact h.bij.comp ih
  have hinj : ∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y := fun k x y e => (hk k).1 e
  have hred : ∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0 := by
    intro x n e
    apply hinj n
    have hlt : n < p ^ n := Nat.lt_pow_self hp.one_lt
    rw [pow_eq_zero_of_le hlt.le e, zero_pow (pow_ne_zero n hp.ne_zero)]
  refine ⟨⟨RingEquiv.ofBijective F h.bij, fun x => rfl⟩, hred, fun k x => (hk k).2 x, hinj, ?_⟩
  intro r hr
  have hroot : ∀ k, r k ^ p ^ k = r 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hr k, ih]
  refine ⟨?_, hroot, ?_⟩
  · intro k
    refine ⟨r (k + 1) ^ (p - 2), ?_⟩
    have h2 : p = (p - 2) + 1 + 1 := by have := hp.two_le; omega
    conv_lhs => rw [← hr k, h2]
    rw [pow_succ, pow_succ]
  · intro N x e k
    apply hred _ (p ^ k * N + 1)
    calc (r k * x) ^ (p ^ k * N + 1)
        = r k ^ (p ^ k * N + 1) * x ^ (p ^ k * N + 1) := mul_pow _ _ _
      _ = r k * x ^ (p ^ k * N) * (r 0 ^ N * x) := by
          rw [pow_succ (r k), pow_mul, hroot k, pow_succ x]
          ring
      _ = 0 := by rw [e, mul_zero]

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PieceMeasureLtTop
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem entries_isCompact {A : Type} [TopologicalSpace A] {m n : ℕ} {C : Set A} (hC : IsCompact C) :
    IsCompact {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} := by
  have h : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have e : {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} =
      Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C)) := by
    ext M
    exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ p) q (Set.mem_univ q)⟩
  rw [e]
  exact h

theorem exists_compact_comb {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ)
    {C₁ C₂ C₃ : Set A} (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (h₃ : IsCompact C₃) :
    ∃ D : Set A, IsCompact D ∧ ∀ (x : A) (b d : Fin n → A), x ∈ C₁ → (∀ k, b k ∈ C₂) → (∀ k, d k ∈ C₃) →
      x + ∑ k, b k * d k ∈ D := by
  have hK : IsCompact (C₁ ×ˢ ((Set.pi Set.univ (fun _ : Fin n => C₂)) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => C₃)))) :=
    h₁.prod ((isCompact_univ_pi fun _ => h₂).prod (isCompact_univ_pi fun _ => h₃))
  have hc : Continuous (fun w : A × (Fin n → A) × (Fin n → A) => w.1 + ∑ k, w.2.1 k * w.2.2 k) := by
    fun_prop
  refine ⟨_, hK.image hc, fun x b d hx hb hd => ⟨(x, b, d), ⟨hx, ?_, ?_⟩, rfl⟩⟩
  · exact fun k _ => hb k
  · exact fun k _ => hd k

theorem piece_measure_lt_top : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
    [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A)
    (_ : IsCompact C) (_ : (0 : A) ∈ C) (ν : Measure (Fx A a r × Fx A a t)) (_ : IsFiniteMeasureOnCompacts ν), ν (Piece e f P i C) < ∞ := by
  intro A _ _ _ a r t _ _ e f P i C hC h0 ν _
  obtain ⟨D₃, hD₃, h₃⟩ := exists_compact_comb (A := A) t hC hC hC
  have hS : IsCompact ((fun w : A × A => w.1 + w.2) '' (C ×ˢ C)) :=
    (hC.prod hC).image continuous_add
  obtain ⟨D, hD, hDm⟩ := exists_compact_comb (A := A) r (hC.union hD₃) hC hS
  refine lt_of_le_of_lt (measure_mono ?_)
    (((entries_isCompact (m := a) (n := r) hC).prod (entries_isCompact (m := a) (n := t) hD)).measure_lt_top)
  rintro z ⟨-, hz, hy, hv, hvi, c, hci, hc, hcv⟩
  refine ⟨hz, fun p k => ?_⟩
  have hyk : ∀ l, yc P z l k ∈ (fun w : A × A => w.1 + w.2) '' (C ×ˢ C) := fun l =>
    ⟨(f * yc P z l k, (1 - f) * yc P z l k), ⟨(hy l k).1, (hy l k).2⟩, by simp only; ring⟩
  have hvk : vc P z p k ∈ C ∪ D₃ := by
    by_cases hk : k = i
    · subst hk
      right
      have hmem := h₃ ((1 - f) * vc P z p k) c (fun j => if j = k then 0 else vc P z p j) (hvi p)
        (fun j => (hc j).2) (fun j => by
          by_cases hj : j = k
          · simpa [hj] using h0
          · simpa [hj] using hv p j hj)
      have hsum : ∑ j, c j * (if j = k then 0 else vc P z p j) = f * vc P z p k := by
        rw [hcv p]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = k
        · subst hj
          simp [hci]
        · simp [hj]
      rw [hsum] at hmem
      have hE : (1 - f) * vc P z p k + f * vc P z p k = vc P z p k := by ring
      rwa [hE] at hmem
    · exact Or.inl (hv p k hk)
  have hE : z.2 p k = vc P z p k + ∑ l, z.1 p l * yc P z l k := by
    simp [vc, Matrix.sub_apply, Matrix.mul_apply]
  rw [hE]
  exact hDm _ _ _ hvk (fun l => hz p l) hyk

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtraction
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValPowDvd

theorem dvd_of_pow_mul_dvd_pow : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  intro S _ ϖ hϖ hV z m d hd hdiv
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨e, he, h1, h2⟩ := hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1) := by rw [hc']
  rw [mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul] at h3
  have key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0 := by linear_combination h3
  have he' : e = w * c' ^ (d' + 1) :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)
  have hee : e * e = e := he.eq
  exact ⟨e * w * c' ^ d' + c, by
    linear_combination (-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' +
      (w * c' ^ d' * ϖ ^ m) * hee⟩

end GlobalTheory.CompanionTheory.ValPowDvd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpenStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_neighbourhoods_shrink_compact_open : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | exact GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | (intros; apply GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZeroStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen <;> assumption)
end

