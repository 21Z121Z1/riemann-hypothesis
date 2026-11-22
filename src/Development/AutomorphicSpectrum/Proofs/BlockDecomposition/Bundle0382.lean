import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntEl

open MeasureTheory

theorem finite_range {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem measure_level_ne_top {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [AddCommGroup W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ : X → W} (hc : HasCompactSupport φ) {v : W}
    (hv : v ≠ 0) : μ (φ ⁻¹' {v}) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, show φ x = v from hx]
  exact hv

theorem smInt_comp {X Y W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X)
    (ψ : X → Y) (g : Y → W) (S : Finset Y) (hS : ∀ x, ψ x ∈ S)
    (hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})) (hf : ∀ y ∈ S, g y ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤) :
    smInt μ (g ∘ ψ) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • g y := by
  classical
  have hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v)
      ⊆ ↑(S.image g) := by
    intro v hv
    by_contra hvS
    apply hv
    have : (g ∘ ψ) ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))
    simp [this]
  unfold smInt
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
      (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero]
    symm
    exact Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]
  · have hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion,
        Finset.mem_filter, exists_prop]
      constructor
      · intro hx
        exact ⟨ψ x, ⟨hS x, hx⟩, rfl⟩
      · rintro ⟨y, ⟨_, hy⟩, rfl⟩
        exact hy
    have hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y}) := by
      rw [hset]
      refine measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1
      intro a _ b _ hab
      exact Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)
    rw [hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1
      (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]

theorem smInt_add {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ₁ φ₂ : X → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂ := by
  classical
  let ψ : X → W × W := fun x => (φ₁ x, φ₂ x)
  let S : Finset (W × W) := (finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset
  have hS : ∀ x, ψ x ∈ S := fun x =>
    Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩,
      (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y}) := fun y _ =>
    ((l₁.prodMk l₂).isOpen_fiber y).measurableSet
  have f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by
      show φ₁ x = y.1
      rw [← show ψ x = y from hx])
  have f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by
      show φ₂ x = y.2
      rw [← show ψ x = y from hx])
  have e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2) :=
    smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by
      by_cases h : y.1 = 0
      · refine f₂ y fun h' => hy ?_
        show y.1 + y.2 = 0
        rw [h, h', add_zero]
      · exact f₁ y h
  have e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1 :=
    smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy
  have e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2 :=
    smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => smul_add _ _ _

theorem smInt_linear {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (T : W →ₗ[ℂ] W') {φ : X → W}
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    smInt μ (T ∘ φ) = T (smInt μ φ) := by
  classical
  let S : Finset W := (finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y}) := fun y _ => (l.isOpen_fiber y).measurableSet
  have e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y :=
    smInt_comp μ φ T S hS hm fun y _ hy =>
      measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])
  have e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y :=
    smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy
  rw [e₀, e₁, map_sum]
  exact Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm

theorem smInt_comp_measurePreserving {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X) {c : X → X} {φ : X → W}
    (hc : MeasurePreserving c μ μ) (l : IsLocallyConstant φ) :
    smInt μ (φ ∘ c) = smInt μ φ := by
  unfold smInt
  refine finsum_congr fun v => ?_
  have h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v}) :=
    hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet
  rw [Set.preimage_comp, h]

theorem smInt_indicator {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W]
    (μ : Measure X) (A : Set X) (v : W) :
    smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  classical
  unfold smInt
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have : (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅ := by
        ext x
        simp [Set.indicator_zero', Ne.symm hw]
      rw [this, measure_empty]
      simp
  · rw [finsum_eq_single _ v]
    · have : (A.indicator fun _ => v) ⁻¹' {v} = A := by
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, Ne.symm hv]
      rw [this]
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, smul_zero]
      · have : (A.indicator fun _ => v) ⁻¹' {w} = ∅ := by
          ext x
          by_cases hx : x ∈ A
          · simp [hx, Ne.symm hw]
          · simp [hx, Ne.symm hw0]
        simp [this]

theorem smInt_properties : ∀ {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ], (∀ φ₁ φ₂ : X → W, IsLocallyConstant φ₁ → HasCompactSupport φ₁ → IsLocallyConstant φ₂ → HasCompactSupport φ₂ → smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂) ∧ (∀ (T : W →ₗ[ℂ] W') (φ : X → W), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (T ∘ φ) = T (smInt μ φ)) ∧ (∀ (c : X → X) (φ : X → W), MeasureTheory.MeasurePreserving c μ μ → IsLocallyConstant φ → smInt μ (φ ∘ c) = smInt μ φ) ∧ ∀ (A : Set X) (v : W), IsCompact A → IsOpen A → IsClosed A → smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  intro X W W' _ _ _ _ _ _ _ μ _
  exact ⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂,
    fun T φ l c => smInt_linear μ T l c,
    fun c φ hc l => smInt_comp_measurePreserving μ hc l,
    fun A v _ _ _ => smInt_indicator μ A v⟩

end GlobalTheory.CompanionTheory.Rodier.SmIntEl

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.PiCoinv

section Modules

variable {α : Type} {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def pureSpan (K : ∀ a, Submodule ℂ (X a)) : Submodule ℂ (⨂[ℂ] a, X a) :=
  Submodule.span ℂ {t | ∃ (x : ∀ a, X a) (a : α), x a ∈ K a ∧ t = PiTensorProduct.tprod ℂ x}

theorem tprod_sub_mem [Fintype α] (K : ∀ a, Submodule ℂ (X a)) {x y : ∀ a, X a}
    (h : ∀ a, x a - y a ∈ K a) :
    PiTensorProduct.tprod ℂ x - PiTensorProduct.tprod ℂ y ∈ pureSpan K := by
  classical
  have key : ∀ s : Finset α, PiTensorProduct.tprod ℂ x -
      PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) ∈ pureSpan K := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro b s hb ih
      have hx : Function.update (fun a => if a ∈ s then y a else x a) b (x b) =
          (fun a => if a ∈ s then y a else x a) := by
        rw [Function.update_eq_self_iff]
        simp [hb]
      have hupd : (fun a => if a ∈ insert b s then y a else x a) =
          Function.update (fun a => if a ∈ s then y a else x a) b (y b) := by
        funext a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Function.update_of_ne hab, Finset.mem_insert, hab]
      have e : PiTensorProduct.tprod ℂ
            (Function.update (fun a => if a ∈ s then y a else x a) b (x b - y b)) =
          PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
            PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) := by
        rw [MultilinearMap.map_update_sub, hx, hupd]
      have hmem : PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
          PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) ∈ pureSpan K := by
        rw [← e]
        exact Submodule.subset_span ⟨_, b, by simpa using h b, rfl⟩
      have := Submodule.add_mem _ ih hmem
      rwa [sub_add_sub_cancel] at this
  simpa using key Finset.univ

def rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) : X a :=
  Function.surjInv (Submodule.mkQ_surjective (K a)) (q a)

theorem mkQ_rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) :
    (K a).mkQ (rep K q a) = q a := by
  unfold rep
  exact Function.surjInv_eq (Submodule.mkQ_surjective (K a)) (q a)

def descendFun (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) : (⨂[ℂ] a, X a) ⧸ pureSpan K :=
  (pureSpan K).mkQ (PiTensorProduct.tprod ℂ (rep K q))

theorem descendFun_eq [Fintype α] (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (y : ∀ a, X a)
    (hy : ∀ a, (K a).mkQ (y a) = q a) :
    descendFun K q = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ y) := by
  unfold descendFun
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact tprod_sub_mem K fun a => (Submodule.Quotient.eq _).1 ((mkQ_rep K q a).trans (hy a).symm)

theorem mkQ_update [DecidableEq α] (K : ∀ a, Submodule ℂ (X a)) {q : ∀ a, X a ⧸ K a} {y : ∀ a, X a}
    (hy : ∀ a, (K a).mkQ (y a) = q a) (a : α) {w : X a} {r : X a ⧸ K a} (hw : (K a).mkQ w = r) (b : α) :
    (K b).mkQ (Function.update y a w b) = Function.update q a r b := by
  by_cases hb : b = a
  · subst hb
    simp [hw]
  · simp [Function.update_of_ne hb, hy]

def descend [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    MultilinearMap ℂ (fun a => X a ⧸ K a) ((⨂[ℂ] a, X a) ⧸ pureSpan K) where
  toFun := descendFun K
  map_update_add' := by
    intro _ q a u v
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    obtain ⟨sv, hv⟩ := Submodule.mkQ_surjective (K a) v
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := su + sv) (by rw [map_add, hu, hv])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), descendFun_eq K _ _ (mkQ_update K hy a hv),
      MultilinearMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ q a c u
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := c • su) (by rw [map_smul, hu])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), MultilinearMap.map_update_smul, map_smul]

def quotMap (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) →ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  (pureSpan K).liftQ (PiTensorProduct.map fun a => (K a).mkQ) (Submodule.span_le.2 (by
    rintro _ ⟨x, a, hx, rfl⟩
    show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ x) = 0
    rw [PiTensorProduct.map_tprod]
    exact MultilinearMap.map_coord_zero _ a ((Submodule.Quotient.mk_eq_zero _).2 hx)))

def quotEquiv [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) ≃ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  LinearEquiv.ofLinear (quotMap K) (PiTensorProduct.lift (descend K))
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      show quotMap K (PiTensorProduct.lift (descend K) (PiTensorProduct.tprod ℂ q)) =
        PiTensorProduct.tprod ℂ q
      rw [PiTensorProduct.lift.tprod]
      show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ (rep K q)) = _
      rw [PiTensorProduct.map_tprod]
      exact congrArg _ (funext (mkQ_rep K q)))
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      show PiTensorProduct.lift (descend K) (PiTensorProduct.map (fun a => (K a).mkQ)
        (PiTensorProduct.tprod ℂ x)) = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ x)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
      exact descendFun_eq K _ x fun _ => rfl)

end Modules

section Reps

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

theorem twKer_piTensor_le (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) ≤ pureSpan fun a => twKer (π a) (H a) (χ a) := by
  unfold twKer
  apply Submodule.span_le.2
  rintro _ ⟨n, v, rfl⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.tprod ℂ (fun a => π a ((n : ∀ a, Γ a) a) (x a)) := by
      show PiTensorProduct.map (fun a => π a ((n : ∀ a, Γ a) a)) (PiTensorProduct.tprod ℂ x) = _
      rw [PiTensorProduct.map_tprod]
    have e2 : ((piChar χ n : ℂˣ) : ℂ) =
        ∏ a, ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ) := by
      rw [← Units.coe_prod]
      rfl
    have e3 := (MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ)
      (fun a => ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)) x).symm
    rw [map_smul, smul_comm, ← smul_sub]
    apply Submodule.smul_mem
    rw [e1, e2, e3]
    apply tprod_sub_mem
    intro a
    apply Submodule.subset_span
    exact ⟨⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩, x a, rfl⟩
  | add v₁ v₂ h₁ h₂ =>
    rw [map_add, smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂

theorem pureSpan_le_twKer (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    (pureSpan fun a => twKer (π a) (H a) (χ a)) ≤ twKer (piTensor π) (piSub H) (piChar χ) := by
  classical
  apply Submodule.span_le.2
  rintro _ ⟨x, a, hx, rfl⟩
  have key : ∀ u ∈ twKer (π a) (H a) (χ a),
      PiTensorProduct.tprod ℂ (Function.update x a u) ∈ twKer (piTensor π) (piSub H) (piChar χ) := by
    intro u hu
    unfold twKer at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, v, rfl⟩ := hu
      have hn : Pi.mulSingle a (g : Γ a) ∈ piSub H := by
        refine (Subgroup.mem_pi _).2 fun b _ => ?_
        by_cases hb : b = a
        · subst hb
          simp
        · rw [Pi.mulSingle_eq_of_ne hb]
          exact one_mem _
      let n : piSub H := ⟨Pi.mulSingle a (g : Γ a), hn⟩
      have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (π a (g : Γ a) v)) := by
        show PiTensorProduct.map (fun b => π b ((n : ∀ a, Γ a) b))
          (PiTensorProduct.tprod ℂ (Function.update x a v)) = _
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb
          simp [n]
        · simp [n, Function.update_of_ne hb, Pi.mulSingle_eq_of_ne hb]
      have e2 : ((piChar χ n : ℂˣ) : ℂ) = ((χ a g : ℂˣ) : ℂ) := by
        have hu : (piChar χ n : ℂˣ) = ∏ b, χ b ⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ := rfl
        rw [hu, Finset.prod_eq_single a]
        · have : (⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : H a) = g := Subtype.ext (by simp [n])
          rw [this]
        · intro b _ hb
          have : (⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ : H b) = 1 :=
            Subtype.ext (by simp [n, Pi.mulSingle_eq_of_ne hb])
          rw [this, map_one]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have hw : PiTensorProduct.tprod ℂ (Function.update x a ((π a) (g : Γ a) v - ((χ a g : ℂˣ) : ℂ) • v)) =
          (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) -
            ((piChar χ n : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ (Function.update x a v) := by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, e1, e2]
      rw [hw]
      exact Submodule.subset_span ⟨n, _, rfl⟩
    | zero =>
      rw [MultilinearMap.map_update_zero]
      exact Submodule.zero_mem _
    | add u₁ u₂ _ _ h₁ h₂ =>
      rw [MultilinearMap.map_update_add]
      exact Submodule.add_mem _ h₁ h₂
    | smul c u _ h =>
      rw [MultilinearMap.map_update_smul]
      exact Submodule.smul_mem _ c h
  have := key (x a) hx
  rwa [Function.update_eq_self] at this

theorem twKer_piTensor_eq (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) = pureSpan fun a => twKer (π a) (H a) (χ a) := by
  exact le_antisymm (twKer_piTensor_le π H χ) (pureSpan_le_twKer π H χ)

end Reps

theorem twJacquet_piTensor_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  intro α _ Γ X _ _ _ π H χ
  exact ⟨(Submodule.quotEquivOfEq _ _ (twKer_piTensor_eq π H χ)).trans
    (quotEquiv fun a => twKer (π a) (H a) (χ a))⟩

end GlobalTheory.CompanionTheory.Rodier.PiCoinv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS

theorem stepWtSpan : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  intro n ε S hSf hSD hSK N _ _ e he
  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hE : IsGlRep (smE ε (rreg ε)) := hD.glRep
  have hKU : IsKUnitary ε (smE ε (rreg ε)) :=
    isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S := hSK
  haveI := hSf
  haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype) :=
    isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv =>
      ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩
  let T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)
  have hTs : ∀ c, (T c).IsSymmetric := fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))
  have hcomm : Pairwise (Function.onFun Commute T) := fun a c _ =>
    LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  let e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N :=
    e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap
  by_contra hno
  push_neg at hno
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e' := by
    intro χ x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε)) := fun c =>
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))
    have hx0' : (x : smD ε (rreg ε)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) =
        (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε)) := fun c =>
      (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))
    exact hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x)
      ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)
  have hker : LinearMap.ker e' = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
  refine he (LinearMap.ext fun y => ?_)
  have hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e' := hker ▸ Submodule.mem_top
  have h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0 := hy
  calc e y = e (Submodule.comapSubtypeEquivOfLe hSD ((Submodule.comapSubtypeEquivOfLe hSD).symm y)) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = 0 := h2

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

