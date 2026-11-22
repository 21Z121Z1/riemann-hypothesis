import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AnalyticAtEvalConeComp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem analyticAt_evalCone_comp {ι : Type} [Fintype ι] {n : ι → ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : E → Cone n ℂ) (u₀ : E) (hz : ∀ k i, AnalyticAt ℂ (fun u ↦ z u k i) u₀)
    (f : MvPolynomial (Coord n) ℤ) : AnalyticAt ℂ (fun u ↦ evalCone (z u) f) u₀ := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun u ↦ evalCone (z u) (C a)) = fun _ ↦ ((a : ℤ) : ℂ) := by
      funext u; rw [evalCone, eval₂_C]; simp
    rw [h]; exact analyticAt_const
  | add p q hp hq =>
    have h : (fun u ↦ evalCone (z u) (p + q)) = fun u ↦ evalCone (z u) p + evalCone (z u) q := by
      funext u; simp [evalCone]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun u ↦ evalCone (z u) (p * X v)) = fun u ↦ evalCone (z u) p * z u v.1 v.2 := by
      funext u; simp [evalCone]
    rw [h]; exact hp.mul (hz v.1 v.2)

theorem PlurisubharmonicMetric.proof (hPts : ConePoints.Statement) (hMet : ChartMetric.Statement) : PlurisubharmonicMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG e γ u₀ hγ hev
  have hw₀ : γ u₀ ∈ D.extPoints := hev.self_of_nhds
  obtain ⟨hz₀, la₀, hla₀, hrel₀⟩ := (hPts ι n P D d g hg).2 _ hw₀

  choose c hc using fun k ↦ Function.ne_iff.mp (hz₀.1 k)
  have hm₀ : evalCone (D.basePart₂ (γ u₀)) (chartMonomial c d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw₀.1 none)
  have hj' : D.newPart (γ u₀) j ≠ 0 := hj
  have hg₀ : evalCone (D.basePart₂ (γ u₀)) (g c j) ≠ 0 := by
    intro h0
    apply hj'
    rw [hrel₀ c hm₀ j, h0, mul_zero, zero_div]

  have hco : ∀ (o : Option ι) (i : Fin (D.extSizes o + 1)), AnalyticAt ℂ (fun u ↦ γ u o i) u₀ :=
    fun o i ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D.extSizes o + 1) ↦ ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) o).analyticAt _).comp hγ)
  have hold : ∀ f, AnalyticAt ℂ (fun u ↦ evalCone (D.basePart₂ (γ u)) f) u₀ :=
    analyticAt_evalCone_comp (fun u ↦ D.basePart₂ (γ u)) u₀ fun k i ↦ hco (some k) i
  have hM := hold (chartMonomial c d)
  have hG' := hold (g c j)
  have hnew : AnalyticAt ℂ (fun u ↦ D.newPart (γ u) j) u₀ := hco none j
  refine ⟨fun u ↦ D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
      evalCone (D.basePart₂ (γ u)) (g c j), (hnew.mul hM).div hG' hg₀, ?_, ?_⟩
  · simp only
    rw [hrel₀ c hm₀ j]
    field_simp
    exact hla₀
  · filter_upwards [hev, hM.continuousAt.eventually_ne hm₀, hG'.continuousAt.eventually_ne hg₀]
      with u hu hmu hgu
    obtain ⟨_, la, _, hrel⟩ := (hPts ι n P D d g hg).2 _ hu
    have hla : D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
        evalCone (D.basePart₂ (γ u)) (g c j) = la := by
      rw [hrel c hmu j]
      field_simp
    rw [hla]
    exact (hMet ι n P D N hN d g hg r G δ hG).2 _ hu c la hmu (hrel c hmu)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.BirationalOfBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace BlockImage

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in

theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff, heq_iff_eq, true_and] at h
  rw [h]

omit [Fintype ι] [DecidableEq ι] in

theorem const_injective (k₀ : ι) : Function.Injective (fun _ : Unit ↦ k₀) := fun _ _ _ ↦ rfl

omit [Fintype ι] in

theorem rename_component (k₀ : ι) (m : Unit → ℕ) (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    rename (blockIncl k₀) (weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ n k₀) m f) =
      weightedHomogeneousComponent (coordDeg n) (Function.extend (fun _ : Unit ↦ k₀) m 0)
        (rename (blockIncl k₀) f) :=
  FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (ι := blockIdx fun _ : Unit ↦ n k₀)
    (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl)
    (const_injective k₀) (blockIncl_injective k₀) m f

def projVariety (P : ArithVariety n) (k₀ : ι) : ArithVariety (fun _ : Unit ↦ n k₀) where
  ideal := P.projIdeal k₀
  isPrime := by
    have := P.isPrime
    exact Ideal.comap_isPrime _ _
  homogeneous f hf m := by
    change rename (blockIncl k₀) _ ∈ P.ideal
    rw [rename_component]
    exact P.homogeneous _ hf _
  relevant k := by
    obtain ⟨i, hi⟩ := P.relevant k₀
    refine ⟨i, fun h ↦ hi ?_⟩
    change rename (blockIncl k₀) (X ⟨k, i⟩) ∈ P.ideal at h
    rwa [rename_X] at h
  horizontal a ha := by
    change rename (blockIncl k₀) (C a) ∈ P.ideal at ha
    rw [rename_C] at ha
    exact P.horizontal a ha

variable {Ω : Type} [Field Ω]

omit [Fintype ι] [DecidableEq ι] in

theorem mConeMap_rename (y : Coord n → Ω) (k₀ : ι)
    (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (rename (blockIncl k₀) f) =
      rename (fun _ : Unit ↦ k₀)
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) f) := by
  have h : ((Geo.mConeMap (ι := blockIdx n) y).comp (rename (blockIncl k₀))) =
      ((rename (R := Ω) (fun _ : Unit ↦ k₀)).restrictScalars ℤ).comp
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) := by
    refine MvPolynomial.algHom_ext fun v ↦ ?_
    simp [Geo.mConeMap, blockIncl]
  exact congrArg (fun φ : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ f) h

omit [Fintype ι] [DecidableEq ι] in

theorem comap_mCoordIdeal (y : Coord n → Ω) (k₀ : ι) :
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
      Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) := by
  ext f
  simp only [Ideal.mem_comap, Geo.mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_rename]
  exact map_eq_zero_iff _ (rename_injective _ (const_injective k₀))

theorem algebraMap_injective {K : Type} {κ : K → Type} (I : Ideal (Geo.MRing κ))
    (h : Geo.IsHorizontal I) : Function.Injective (algebraMap ℤ (Geo.MRing κ ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* Geo.MRing κ) := ha
  rw [show I.comap (C : ℤ →+* Geo.MRing κ) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

omit [Fintype ι] in

theorem birational_of_block (y : Coord n → Ω) (k₀ : ι)
    (hB : Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) :
    Geo.Birational (ι := blockIdx n) y := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hB s
  have hom : ∀ f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ,
      Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ n k₀) f d →
      Geo.IsMultiHomog (ι := blockIdx n) (rename (blockIncl k₀) f)
        (Function.extend (fun _ : Unit ↦ k₀) d 0) := by
    intro f hf
    rw [← Bridge.isMultiHomog_iff] at hf ⊢
    have hf' : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ n k₀) f d := hf
    rw [← hf'.weightedHomogeneousComponent_same, rename_component]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  refine ⟨Function.extend (fun _ : Unit ↦ k₀) d 0, rename (blockIncl k₀) g, rename (blockIncl k₀) h,
    hom g hg, hom h hh, ?_, ?_⟩
  · rw [aeval_rename]
    exact hne
  · rw [aeval_rename, aeval_rename]
    exact heq

end BlockImage

open BlockImage in

theorem BlockImage.proof (hDim : IntDomainDim.Statement) (hTr : ConeTrdeg.Statement) :
    BlockImage.Statement := by
  refine ⟨fun ι _ _ n P k₀ ↦ ⟨projVariety P k₀, rfl⟩, ?_⟩
  intro ι _ _ n Ω _ y k₀ D hA
  refine ⟨comap_mCoordIdeal y k₀, fun hB ↦ ?_⟩
  obtain ⟨-, hMP, hHor, hKd⟩ := hA
  rw [← comap_mCoordIdeal y k₀]
  have hMP' : Geo.IsMultiProjPrime (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP ⊢
    refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename
      (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀)
      (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) ?_ hMP
    rintro ⟨k, i⟩ ⟨u, hu⟩
    obtain rfl : k₀ = k := hu
    exact ⟨⟨(), i⟩, rfl⟩
  have hHor' : Geo.IsHorizontal (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor
    simp only [Ideal.mem_comap]
    rw [rename_C]
  refine ⟨inferInstance, hMP', hHor', ?_⟩

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hMP.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    simp [Geo.mConeMap, h0]
  rw [comap_mCoordIdeal y k₀] at hHor' hMP' ⊢
  have := hMP.1
  have := hMP'.1
  have dimA := hDim _ (algebraMap_injective _ hHor)
  have dimA' := hDim _ (algebraMap_injective _ hHor')
  rw [hTr ι (blockIdx n) Ω y (birational_of_block y k₀ hB) hrel hHor] at dimA
  rw [hTr Unit (blockIdx fun _ : Unit ↦ n k₀) Ω _ hB (fun _ ↦ hrel k₀) hHor'] at dimA'
  rw [hKd] at dimA
  have h1 : ((D + 1 + Fintype.card ι : ℕ) : ℕ∞) =
      (Algebra.trdeg ℤ Ω + Fintype.card ι).toENat + 1 := by exact_mod_cast dimA
  simp only [map_add, map_natCast] at h1
  have key : (Algebra.trdeg ℤ Ω).toENat = D := by
    generalize (Algebra.trdeg ℤ Ω).toENat = t at h1 ⊢
    induction t using ENat.recTopCoe with
    | top => simp at h1
    | coe m =>
      norm_cast at h1 ⊢
      omega
  rw [dimA']
  simp only [map_add, map_natCast, Fintype.card_unit, key]
  norm_cast

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.CardLeOfSeparated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module Function
open scoped ENNReal

noncomputable section

theorem LatticePacking.card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ ρ) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * ρ + δ) / δ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hR : 0 < ρ + δ / 2 := by linarith
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : (⋃ c ∈ s, ball (c : E) (δ / 2)) ⊆ ball (0 : E) (ρ + δ / 2) := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs x hx]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1)
          = μ (⋃ c ∈ s, ball (c : E) (δ / 2)) := by
        rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ2]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (ρ + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hR]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ finrank ℝ E ≤ (ρ + δ / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hR.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ2.le _),
      ENNReal.toReal_natCast] at this
  have e : (2 * ρ + δ) / δ = (ρ + δ / 2) / (δ / 2) := by
    rw [div_eq_div_iff hδ.ne' hδ2.ne']; ring
  rw [e, div_pow, le_div_iff₀ (pow_pos hδ2 _)]
  exact K

theorem LatticePacking.proof : LatticePacking.Statement := by
  intro V _ _ L hL B hB hmin
  classical
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  have : IsAddTorsionFree V := .of_module_rat _
  have : Module.IsTorsionFree ℤ L :=
    Injective.moduleIsTorsionFree (R := ℤ) (fun y : L => (y : V)) Subtype.val_injective
      (fun _ _ => rfl)
  set δ : ℝ := Real.exp (-B) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by rw [hδdef, Real.exp_le_one_iff]; linarith
  let b := Module.Free.chooseBasis ℤ L
  let f : Module.Free.ChooseBasisIndex ℤ L → V := fun i => ((b i : L) : V)
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range f)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  have hdim : finrank ℝ W ≤ finrank ℤ L := by
    exact (finrank_range_le_card (R := ℝ) f).trans
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).ge
  have hW : ∀ x ∈ L, x ∈ W := by
    intro x hx
    have h1 : x = ∑ i, b.repr ⟨x, hx⟩ i • f i := by
      calc x = ((⟨x, hx⟩ : L) : V) := rfl
        _ = L.subtype (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, b.repr ⟨x, hx⟩ i • f i := by rw [map_sum]; rfl
    rw [h1]
    exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  set S : Set V := {x : V | x ∈ L ∧ ‖x‖ ≤ 1} with hS
  set C : ℝ := ((2 * 1 + δ) / δ) ^ finrank ℝ W with hC
  have key : ∀ t : Finset V, (t : Set V) ⊆ S → (t.card : ℝ) ≤ C := by
    intro t ht
    have hcard : (t.subtype (· ∈ W)).card = t.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem]
      intro x hx
      exact hW x (ht hx).1
    rw [← hcard]
    refine LatticePacking.card_le_of_separated (t.subtype (· ∈ W)) hδ zero_le_one ?_ ?_
    · intro c hc
      rw [Finset.mem_subtype] at hc
      simpa using (ht hc).2
    · intro c hc d hd hcd
      rw [Finset.mem_subtype] at hc hd
      have hne : (c : V) - d ≠ 0 := sub_ne_zero.mpr fun h' => hcd (Subtype.ext h')
      have := hmin ((c : V) - d) (L.sub_mem (ht hc).1 (ht hd).1) hne
      simpa using this
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊C⌋₊ + 1)
    have h1 := key t ht
    rw [htc] at h1
    push_cast at h1
    have hC0 : 0 ≤ C := pow_nonneg (div_nonneg (by linarith) hδ.le) _
    linarith [Nat.lt_floor_add_one C]
  refine ⟨hfin, ?_⟩
  have h1 : (S.ncard : ℝ) ≤ C := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  refine h1.trans ?_
  have hq : (2 * 1 + δ) / δ ≤ 5 / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
  have h5 : 1 ≤ 5 / δ := by rw [le_div_iff₀ hδ]; linarith
  have he : 5 / δ = Real.exp (B + Real.log 5) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), hδdef, Real.exp_neg, div_inv_eq_mul, mul_comm]
  calc C ≤ (5 / δ) ^ finrank ℝ W := pow_le_pow_left₀ (div_nonneg (by linarith) hδ.le) hq _
    _ ≤ (5 / δ) ^ finrank ℤ L := pow_le_pow_right₀ h5 hdim
    _ = Real.exp (finrank ℤ L * (B + Real.log 5)) := by rw [he, Real.exp_nat_mul]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartFormEvalAgree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem chartForm_eval_agree (P : ArithVariety n) (A A' : HermLine n) (hdeg : A'.deg = A.deg)
    (hmet : ∀ z ∈ P.points ℂ, A'.metric z = A.metric z)
    (h : ∀ s : IntegralSection P A'.deg,
      (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
          (e e' : MvPolynomial (Coord n) ℤ),
        IsChartForm P A'.deg s.num s.den c d e → IsChartForm P A'.deg s.num s.den c' d' e' →
        (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
          ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A'.metric z) =
            ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A'.metric z)) ∧
        ∃ C : ℝ, s.SupNormLE A' C)
    (s : IntegralSection P A.deg) :
    (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
        (e e' : MvPolynomial (Coord n) ℤ),
      IsChartForm P A.deg s.num s.den c d e → IsChartForm P A.deg s.num s.den c' d' e' →
      (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
        ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) =
          ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A.metric z)) ∧
      ∃ C : ℝ, s.SupNormLE A C := by
  obtain ⟨deg, metric, h1, h2, h3⟩ := A'
  dsimp only at hdeg hmet h
  subst hdeg
  obtain ⟨hind, C, hC⟩ := h s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ ?_, C, fun z hz c d e he hc ↦ ?_⟩
  · rw [← hmet z hz]
    exact hind z hz c c' d d' e e' he he' hc hc'
  · rw [← hmet z hz]
    exact hC z hz c d e he hc

theorem BoundedMonomials.equiv :
    GroundTheory.Heights₂.Heights.BoundedMonomials.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BoundedMonomials.Statement := by
  constructor
  · intro hA ι _ _ n P M k e
    exact hA ι n P (powDivStd M k) e
  · intro hB ι _ _ n P A s
    have hdeg : (powDivStd (twistPow A 1 1 0) 1).deg = A.deg := by
      funext b
      simp [powDivStd, twistPow]
    have hmet : ∀ z ∈ P.points ℂ, (powDivStd (twistPow A 1 1 0) 1).metric z = A.metric z := by
      intro z hz
      have hS := ((HermLine.standard n).metric_pos z hz.1).ne'
      simp only [powDivStd, twistPow, Nat.cast_one, one_mul, mul_zero, neg_zero, Real.exp_zero,
        pow_one]
      field_simp
    exact chartForm_eval_agree P A _ hdeg hmet (hB ι n P (twistPow A 1 1 0) 1) s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartMonomialMemOfNotIsLive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem ArithVariety.chartMonomial_mem_of_not_isLive (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  unfold ArithVariety.IsLive at hc
  push Not at hc
  obtain ⟨k, hk⟩ := hc
  unfold chartMonomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  exact P.ideal.mul_mem_right _ (P.ideal.pow_mem_of_mem hk _ (hd k))

theorem ChartCrossRatio.proof : ChartCrossRatio.Statement := by
  intro ι _ _ n P D d g hg c c' j
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
      ring
    · rw [hg.dead c' hc', mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr
      (P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc hg.pos))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem WeightedDegree.equiv :
    GroundTheory.Heights₂.Heights.WeightedDegree.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.WeightedDegree.Statement := by
  constructor
  · intro h ι _ _ n P D hD a p hp
    have := Fact.mk hp
    exact h ι n P D hD a p
  · intro h ι _ _ n P D hD a p hp
    exact h ι n P D hD a p hp.out

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

