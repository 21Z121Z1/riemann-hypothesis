import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0867
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationQuotientSeparatedDvd
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

theorem main : TwistedDoubleCosetStrictDiagonal → P_asmReg := by
  intro hs1 E _ _ _ hU w hw n a ha b hb ϖ hϖ x hx hc y hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  by_cases h0 : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2
  swap
  · exact absurd (dif_neg h0) hs
  rw [dif_pos h0] at hs
  by_cases h1 : (symIdx n (a % 2 = 1) s).card = a
  swap
  · exact absurd (dif_neg h1) hs
  rw [dif_pos h1] at hs
  by_cases h2 : (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a
  swap
  · exact absurd (dif_neg h2) hs
  rw [dif_pos h2] at hs
  have hd1 : dcos a w (tdiag ϖ (restr x _ h1)) y.1 ≠ 0 := fun h => hs (by rw [h]; simp)
  have hd2 : dcos (n - a) w (tdiag ϖ (restr x _ h2)) y.2 ≠ 0 := fun h => hs (by rw [h]; simp)
  obtain ⟨-, -, u₁, hQ₁, hu₁⟩ := hs1 hU w hw ϖ hϖ a _ (restr_strictAnti hx _ h1) y.1 ⟨1, by simpa using hd1⟩
  obtain ⟨-, -, u₂, hQ₂, hu₂⟩ := hs1 hU w hw ϖ hϖ (n - a) _ (restr_strictAnti hx _ h2) y.2 ⟨1, by simpa using hd2⟩
  rw [hQ₁, hQ₂]
  exact localization_quotient_separated_dvd (fun z => ordL z) hx _ _ h1 h2 (symIdx_rev n _ s) (symIdx_rev n _ sᶜ)
    (symIdx_disj n _ _ s (by have := h0.2.2; omega)) u₁ u₂ (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMap
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

section Abstract
open Set
open scoped ENNReal
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

namespace GlobalTheory.CompanionTheory.ArchDom

theorem measurableSet_inter_preimage {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {s : Set α}
    {t : Set β} (hf : ContinuousOn f s) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : Measurable (s.restrict f) := (continuousOn_iff_continuous_restrict.1 hf).measurable
  have := hs.subtype_image (hm ht)
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_le_sum {D n : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (e : OpenPartialHomeomorph Y (V D)) (ρ : Y → ℝ≥0∞) {Z : Set Y}
    (hZ : MeasurableSet Z) (hnull : volume (e.target ∩ e.symm ⁻¹' Z) = 0)
    (P : Fin n → (Fin D → ℂ) → Y) (K : Fin n → Set (Fin D → ℂ)) (hK : ∀ j, MeasurableSet (K j))
    (hP : ∀ j, ContinuousOn (P j) (K j)) (w : Fin n → (Fin D → ℂ) → ℝ≥0∞)
    (hcov : ∀ y ∈ e.source, y ∉ Z → ∃ j, ∃ u ∈ K j, P j u = y)
    (hinj : ∀ j, ∀ u ∈ K j, ∀ u' ∈ K j, P j u ∉ Z → P j u = P j u' → u = u')
    (hdet : ∀ j, ∀ u ∈ K j, P j u ∈ e.source → P j u ∉ Z →
      DifferentiableAt ℝ ((toV D).symm ∘ e ∘ P j) u ∧
      ENNReal.ofReal |(fderiv ℝ ((toV D).symm ∘ e ∘ P j) u).det| * ρ (P j u) ≤ w j u) :
    GlobalTheory.ChartGlue.chartMeas e ρ ≤
      ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hsrc := e.open_source.measurableSet
  let T : Fin n → Set (Fin D → ℂ) := fun j => K j ∩ P j ⁻¹' ((e.source ∩ S) \ Z)
  let G : Fin n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => (toV D).symm ∘ e ∘ P j
  have hT : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) ((hsrc.inter hS).diff hZ)
  have hM : ∀ j, MeasurableSet (K j \ P j ⁻¹' Z) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) hZ.compl
  have hcover : e '' (e.source ∩ S) ⊆
      (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j) := by
    rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inl (GlobalTheory.ChartGlue.mem_over e hy hyZ)
    · obtain ⟨j, u, hu, rfl⟩ := hcov y hy hyZ
      refine Or.inr (mem_iUnion.2 ⟨j, _, ⟨u, ⟨hu, ⟨⟨hy, hyS⟩, hyZ⟩⟩, rfl⟩, ?_⟩)
      simp [G]
  have hterm : ∀ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) ≤
      Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S := by
    intro j
    have hinjG : InjOn (G j) (T j) := by
      rintro u ⟨hu, hR⟩ u' ⟨hu', hR'⟩ h
      have h1 : e (P j u) = e (P j u') := (toV D).symm.injective h
      exact hinj j u hu u' hu' hR.2 (e.injOn hR.1.1 hR'.1.1 h1)
    have hder : ∀ u ∈ T j, HasFDerivWithinAt (G j) (fderiv ℝ (G j) u) (T j) u := fun u hu =>
      (hdet j u hu.1 hu.2.1.1 hu.2.2).1.hasFDerivAt.hasFDerivWithinAt
    have hae : AEMeasurable (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) :=
      (((hP j).mono diff_subset).aemeasurable (hM j)).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [← measurePreserving_toV.setLIntegral_comp_emb (toV D).toHomeomorph.measurableEmbedding,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hT j) hder hinjG,
      Measure.map_apply_of_aemeasurable hae hS, withDensity_apply',
      Measure.restrict_restrict' (hM j)]
    refine (setLIntegral_mono' (hT j) fun u hu => ?_).trans (lintegral_mono_set ?_)
    · have hv : toV D (G j u) = e (P j u) := (toV D).apply_symm_apply _
      have := (hdet j u hu.1 hu.2.1.1 hu.2.2).2
      rw [hv, e.left_inv hu.2.1.1]
      exact this
    · rintro u ⟨hu, hR⟩
      exact ⟨hR.1.2, hu, hR.2⟩
  calc GlobalTheory.ChartGlue.chartMeas e ρ S = ∫⁻ v in e '' (e.source ∩ S), ρ (e.symm v) :=
        GlobalTheory.ChartGlue.chartMeas_apply e ρ hS
    _ ≤ ∫⁻ v in (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ v in e.target ∩ e.symm ⁻¹' Z, ρ (e.symm v)) +
          ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := lintegral_union_le _ _ _
    _ = ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := by
        rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := tsum_fintype _
    _ ≤ ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by rw [Measure.finset_sum_apply]

theorem ofReal_abs_norm_mul_le (d : ℂ) (x : ℝ) (ε : ℤˣ) :
    ENNReal.ofReal |Algebra.norm ℝ d| * ENNReal.ofReal ((ε : ℤ) * x) ≤
      ENNReal.ofReal |‖d‖ ^ 2 * x| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d‖ ^ 2)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using le_abs_self x
  · simpa using neg_le_abs x

end GlobalTheory.CompanionTheory.ArchDom
end Abstract

open GlobalTheory.FinChart in

theorem GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  intro k _ X q σ D T _ A F hF hol Z hZ hnull hsurj hinj B φ hφ ε K hK hKt hKc
  refine iSup_le fun c => ?_
  refine GlobalTheory.CompanionTheory.ArchDom.chartMeas_le_sum c.e _ hZ (hnull c) (fun j => F ∘ (A.chart j).symm) K
    (fun j => (hK j).measurableSet)
    (fun j => hF.comp_continuousOn ((A.chart j).continuousOn_symm.mono (hKt j))) _ ?_ ?_ ?_
  · intro y _ hyZ
    obtain ⟨x, rfl⟩ := hsurj y hyZ
    obtain ⟨j, u, hu, rfl⟩ := hKc x
    exact ⟨j, u, hu, rfl⟩
  · intro j u hu u' hu' hZu h
    exact (A.chart j).symm.injOn (hKt j hu) (hKt j hu') (hinj _ _ hZu h)
  · intro j u hu hsrc _
    obtain ⟨han, hd⟩ := GlobalTheory.T.smooth_weight_pullback_chart_formula A F hF hol φ hφ c j u (hKt j hu) hsrc
    have hG : (toV D).symm ∘ c.e ∘ (F ∘ (A.chart j).symm) =
        c.finChart ∘ F ∘ (A.chart j).symm := rfl
    rw [hG]
    have hdiff := han.differentiableAt
    refine ⟨hdiff.restrictScalars ℝ, ?_⟩
    have hdet : (fderiv ℝ (c.finChart ∘ F ∘ (A.chart j).symm) u).det = Algebra.norm ℝ
        (LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact LinearMap.det_restrictScalars
        (f := (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, hd]
    exact GlobalTheory.CompanionTheory.ArchDom.ofReal_abs_norm_mul_le _ _ ε
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.MixZ

theorem lintegral_logNorm_locDens_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  intro k _ X q σ D T _ A F hF hol B C φ hφ ψ hψ g S Z N W b a d hcov hWb hg hSo hgc hZ j K hKt hKc
  have hGc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hdc : ContinuousOn (locDens A (fun _ => φ.locPot.pullback F hF) j) (A.chart j).target :=
    locDensCont A _ (fun _ => isPotential_pullback_locPot A F hF hol φ hφ) j
  refine hKc.induction_on (p := fun s => ∫⁻ u in s \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    exact (lintegral_mono_set (diff_subset_diff_left hst)).trans_lt ht
  · intro s t hs ht
    rw [union_diff_distrib]
    exact (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
  intro u0 hu0
  obtain ⟨l, hl⟩ := hcov (F ((A.chart j).symm u0))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l))) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn _).preimage hF)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 ⟨hKt hu0, hl⟩
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l)) with hV
  set Bl := Metric.closedBall u0 (r / 2) with hBl
  have hBV : Bl ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact Bl := isCompact_closedBall _ _
  have hBm : MeasurableSet Bl := Metric.isClosed_closedBall.measurableSet
  have hBt : Bl ⊆ (A.chart j).target := hBV.trans inter_subset_left
  refine ⟨Bl, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  have hla : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (a l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (a l) j u hu)).integrableOn_compact_subset hBV hBc
  have hld : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (d l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (d l) j u hu)).integrableOn_compact_subset hBV hBc
  have hψc : ContinuousOn (fun u => ψ.φ (b l) (F ((A.chart j).symm u))) Bl := by
    intro u hu
    have hc : ContinuousAt (ψ.φ (b l)) (F ((A.chart j).symm u)) :=
      (hψ (b l) _ (ptsIn_mono (hWb l) (hBV hu).2)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := F ∘ (A.chart j).symm) hc
      ((hGc u (hBt hu)).mono hBt)
  have hlψ : IntegrableOn (fun u => |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hψc.abs.div_const 2).integrableOn_compact hBc
  have hh : IntegrableOn (fun u => |Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
      |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
      |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hla.abs.add hld.abs).add hlψ
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hdc.mono hBt)
  have hYm : MeasurableSet (Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z) := by
    have hc : Continuous (fun u : Bl => (F ∘ (A.chart j).symm) u.1) :=
      continuousOn_iff_continuous_restrict.1 (hGc.mono hBt)
    have h1 : MeasurableSet (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) :=
      hBm.subtype_image (hc.measurable hZ)
    have h2 : Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z =
        Bl \ (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) := by
      ext u
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact hn hv
      · rintro ⟨hu, hn⟩
        exact ⟨hu, fun hz => hn ⟨⟨u, hu⟩, hz, rfl⟩⟩
    rw [h2]
    exact hBm.diff h1
  have hpt : ∀ u ∈ Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| ≤
      ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
        |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
        |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M := by
    rintro u ⟨huB, huZ⟩
    by_cases hS : F ((A.chart j).symm u) ∈ S
    · rw [indicator_of_mem hS]
      refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
      · rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg l _ (hBV huB).2 hS huZ, Real.norm_eq_abs]
        have h1 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖ -
          Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
          (ψ.φ (b l) (F ((A.chart j).symm u)) / 2)
        have h2 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖)
          (Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
        rw [abs_div, abs_two] at h1
        linarith
      · simpa using hM u huB
    · rw [indicator_of_notMem hS, zero_mul]
      exact zero_le
  calc ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
          ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|
      ≤ ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        setLIntegral_mono' hYm hpt
    _ ≤ ∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        lintegral_mono_set diff_subset
    _ = (∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2)) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top hh.lintegral_lt_top ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MixZ
end

