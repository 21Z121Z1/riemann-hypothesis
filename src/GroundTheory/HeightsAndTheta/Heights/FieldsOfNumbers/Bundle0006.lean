import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractBlocksSplitPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem PFDegree.toIndefiniteRowSideFullHecke (hA : ProjectionFormulaDegree.Statement.{u}) :
    IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} := by
  intro F _ K _ _ L _ _ ι _ ι₂ _ P' hP' n hc hP bs
  have : ∀ s, Fintype (Sum.elim ι ι₂ s) := fun s => match s with
    | .inl k => (inferInstance : Fintype (ι k))
    | .inr l => (inferInstance : Fintype (ι₂ l))
  obtain ⟨-, h⟩ := hA F K (K ⊕ L) Function.Embedding.inl (Sum.elim ι ι₂) P' hP' n
    ((relDim_eq_iff_hasRelDim P' n).mpr hP)
    ((relDim_eq_iff_hasRelDim (IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks ι₂ P') n).mpr hc) bs
  have := hP'.isPrime
  simp only [AddBlockFunctionField.pullDeg_inl, AddBlockFunctionField.relDeg_inl] at h
  exact h

section Split

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

def splitBlockEquiv : K ⊕ blockCompl j ≃ K' :=
  Equiv.ofBijective (Sum.elim j Subtype.val) (by
    refine ⟨?_, fun k' => ?_⟩
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (j.injective h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr ⟨k', h⟩, rfl⟩)

def splitVarEquiv : (Σ s, splitCoord j ι' s) ≃ (Σ k', ι' k') :=
  Equiv.ofBijective (splitVar j ι') (by
    refine ⟨?_, fun ⟨k', i⟩ => ?_⟩
    · rintro ⟨a | a, x⟩ ⟨b | b, y⟩ h
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases j.injective h1
        cases eq_of_heq h2
        rfl
      · exact absurd ⟨a, congrArg Sigma.fst h⟩ b.2
      · exact absurd ⟨b, (congrArg Sigma.fst h).symm⟩ a.2
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases Subtype.ext h1
        cases eq_of_heq h2
        rfl
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨⟨Sum.inl k, i⟩, rfl⟩
      · exact ⟨⟨Sum.inr ⟨k', h⟩, i⟩, rfl⟩)

theorem splitVarEquiv_fst (v : Σ s, splitCoord j ι' s) :
    (splitVarEquiv j ι' v).1 = splitBlockEquiv j v.1 := by
  rcases v with ⟨k | l, i⟩ <;> rfl

theorem contractBlocks_splitPrime {F : Type u} [Field F] (P' : Ideal (MRing ι' F)) :
    IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks (fun l : blockCompl j => ι' l.1) (splitPrime j P') =
      contractPrime j P' := by
  ext p
  unfold IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks splitPrime contractPrime IndefiniteRowSideFullHecke.FieldNumbers.blockIncl
  simp only [Ideal.mem_comap]
  have e : rename (splitVar j ι') (rename (fun x : Σ k, ι' (j k) =>
      (⟨Sum.inl x.1, x.2⟩ : Σ s, splitCoord j ι' s)) p) = rename (blockIncl j ι') p := by
    rw [rename_rename]
    rfl
  exact iff_of_eq (congrArg (· ∈ P') e)

theorem pullDeg_split (b : K → ℤ) :
    IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) b ∘ (splitBlockEquiv j).symm = pullDeg j b := by
  funext k'
  obtain ⟨s, rfl⟩ := (splitBlockEquiv j).surjective k'
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases s with k | l
  · exact (j.injective.extend_apply b 0 k).symm
  · show (0 : ℤ) = Function.extend j b 0 l.1
    rw [Function.extend_apply' _ _ _ (fun h => l.2 h)]
    rfl

theorem relDim_splitPrime {F : Type u} [Field F] [Fintype K] [Fintype K'] [Fintype (blockCompl j)]
    (P' : Ideal (MRing ι' F)) : relDim (splitPrime j P') = relDim P' := by
  have e : MRing (splitCoord j ι') F ⧸ splitPrime j P' ≃+* MRing ι' F ⧸ P' :=
    Ideal.quotientEquiv _ _ (renameEquiv F (splitVarEquiv j ι')).toRingEquiv
      (Ideal.map_comap_of_surjective _ (renameEquiv F (splitVarEquiv j ι')).surjective P').symm
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv e, Fintype.card_congr (splitBlockEquiv j)]

end Split

theorem contract_funField_le (h₁ : RenameMultiHomog.Statement.{u}) {F : Type u} [Field F]
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨Function.extend j d 0, rename (blockIncl j ι') f,
    rename (blockIncl j ι') g, h₁ F K K' j _ ι' _ (fun _ => rfl) f d hf,
    h₁ F K K' j _ ι' _ (fun _ => rfl) g d hg, hgP, ?_⟩
  simp [contractFracMap, contractQuot, map_div₀]
  rfl

theorem PFDegree.split_model_to_place_model (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) (hB : IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0}) :
    ProjectionFormulaDegree.Statement.{u} := by
  classical
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP hc bs
  have := hP'.isPrime
  refine ⟨contract_funField_le h₁ j P', ?_⟩
  have hQ : IsMultiProjPrime (splitPrime j P') :=
    h₃ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' hP'
  have h := hB F K (blockCompl j) (fun k => ι' (j k)) (fun l => ι' l.1) (splitPrime j P') hQ n
    (by
      rw [contractBlocks_splitPrime]
      exact (relDim_eq_iff_hasRelDim _ n).mp hc)
    (by
      refine (relDim_eq_iff_hasRelDim _ n).mp ?_
      rw [relDim_splitPrime]
      exact hP) bs
  rw [← AddBlockFunctionField.relDeg_inl, ← h₄, contractBlocks_splitPrime] at h
  rw [← h]
  have h2 := h₂ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' n
    (fun i => IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) (bs i))
  simp only [pullDeg_split] at h2
  exact h2.symm

theorem PFDegree.equiv (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} ↔ IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} :=
  ⟨PFDegree.toIndefiniteRowSideFullHecke, PFDegree.split_model_to_place_model h₁ h₂ h₃ h₄⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbExactDivide

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical in

theorem component_mul_form {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      if c ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - c) t * s else 0 := by
  have hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) n (a := t) hs'
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact this

theorem exists_sub_component_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s f : MRing ι F} {n : K → ℕ} (hf : IsMultiHomog f n) (hfL : f ∈ I ⊔ Ideal.span {s}) :
    ∃ t : MRing ι F, f - weightedHomogeneousComponent (blockWeight ι) n (t * s) ∈ I := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hfL
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h1 : weightedHomogeneousComponent (blockWeight ι) n (a + t * s) = a + t * s :=
    IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
  have e : a + t * s - weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      weightedHomogeneousComponent (blockWeight ι) n a := by
    rw [sub_eq_iff_eq_add, ← map_add, h1]
  rw [e]
  exact hI a ha n

omit [DecidableEq K] in

theorem mem_colon_span_iff {I : Ideal (MRing ι F)} {s g : MRing ι F} :
    g ∈ I.colon (Ideal.span {s}) ↔ g * s ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    simpa [smul_eq_mul] using h s (Ideal.subset_span rfl)
  · intro h x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [smul_eq_mul, show g * (t * s) = t * (g * s) by ring]
    exact I.mul_mem_left t h

open Classical in

theorem finrank_eq (h1 : GradedFinite.Statement.{u}) [Fintype K] [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {c : K → ℕ} {s : MRing ι F}
    (hs : IsMultiHomog s c) (n : K → ℕ) :
    Module.finrank F (gradedPiece I n) =
      Module.finrank F (gradedPiece (I ⊔ Ideal.span {s}) n) +
        (if c ≤ n then Module.finrank F (gradedPiece (I.colon (Ideal.span {s})) (n - c))
          else 0) := by
  have hIL : I ≤ I ⊔ Ideal.span {s} := le_sup_left
  let π : (MRing ι F ⧸ I) →ₗ[F] (MRing ι F ⧸ (I ⊔ Ideal.span {s})) :=
    (Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ F (I ⊔ Ideal.span {s}))
      (fun a ha => by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hIL ha)).toLinearMap
  have hπ : ∀ x, π (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I ⊔ Ideal.span {s}) x :=
    fun x => rfl
  have : FiniteDimensional F (gradedPiece I n) := (h1 F K ι I n).1
  have hrn := (π.domRestrict (gradedPiece I n)).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (π.domRestrict (gradedPiece I n)) =
      gradedPiece (I ⊔ Ideal.span {s}) n := by
    rw [LinearMap.range_domRestrict, gradedPiece, gradedPiece, ← Submodule.map_comp]
    congr 1

  have hkerdesc : ∀ y ∈ LinearMap.ker (π.domRestrict (gradedPiece I n)),
      ∃ f : MRing ι F, IsMultiHomog f n ∧ f ∈ I ⊔ Ideal.span {s} ∧
        ((y : gradedPiece I n) : MRing ι F ⧸ I) = Ideal.Quotient.mk I f := by
    rintro ⟨y, hy⟩ hker
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hker
    have : π (Ideal.Quotient.mk I f) = 0 := hker
    rwa [hπ, Ideal.Quotient.eq_zero_iff_mem] at this
  rw [← hrange, ← hrn]
  congr 1
  by_cases hc : c ≤ n
  · rw [if_pos hc]
    let W := weightedHomogeneousSubmodule F (blockWeight ι) (n - c)
    let α : W →ₗ[F] (MRing ι F ⧸ I.colon (Ideal.span {s})) :=
      (Ideal.Quotient.mkₐ F (I.colon (Ideal.span {s}))).toLinearMap ∘ₗ W.subtype
    let β : W →ₗ[F] (MRing ι F ⧸ I) :=
      (Ideal.Quotient.mkₐ F I).toLinearMap ∘ₗ (LinearMap.mulRight F s) ∘ₗ W.subtype
    have hker : LinearMap.ker α = LinearMap.ker β := by
      ext g
      simp [α, β, Ideal.Quotient.eq_zero_iff_mem]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : LinearMap.range α = gradedPiece (I.colon (Ideal.span {s})) (n - c) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have e2 : LinearMap.range β =
        (LinearMap.ker (π.domRestrict (gradedPiece I n))).map (gradedPiece I n).subtype := by
      ext x
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩
        have hgs : g * s ∈ weightedHomogeneousSubmodule F (blockWeight ι) n := by
          have := IsWeightedHomogeneous.mul ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg) hs
          rw [tsub_add_cancel_of_le hc] at this
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr this
        refine ⟨⟨(Ideal.Quotient.mkₐ F I).toLinearMap (g * s), Submodule.mem_map_of_mem hgs⟩,
          ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply]
        change π ((Ideal.Quotient.mkₐ F I) (g * s)) = 0
        rw [Ideal.Quotient.mkₐ_eq_mk, hπ, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩)
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
        obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
        rw [component_mul_form hs, if_pos hc] at ht
        refine ⟨⟨weightedHomogeneousComponent (blockWeight ι) (n - c) t,
          weightedHomogeneousComponent_mem _ _ _⟩, ?_⟩
        change Ideal.Quotient.mk I (weightedHomogeneousComponent (blockWeight ι) (n - c) t * s) =
          ((y : gradedPiece I n) : MRing ι F ⧸ I)
        rw [hyf, Ideal.Quotient.eq]
        simpa using I.neg_mem ht
    have eα : LinearMap.range α ≃ₗ[F] LinearMap.range β :=
      α.quotKerEquivRange.symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ β.quotKerEquivRange
    rw [← e1, eα.finrank_eq, e2]
    exact (Submodule.equivMapOfInjective (gradedPiece I n).subtype Subtype.val_injective
      (LinearMap.ker (π.domRestrict (gradedPiece I n)))).finrank_eq
  · rw [if_neg hc]
    have hbot : LinearMap.ker (π.domRestrict (gradedPiece I n)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
      obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
      rw [component_mul_form hs, if_neg hc, sub_zero] at ht
      rw [Submodule.mem_bot]
      apply Subtype.ext
      rw [hyf, ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [hbot, finrank_bot]

theorem proof (h1 : GradedFinite.Statement.{u}) : HilbExactDivide.Statement.{u} := by
  intro F _ K _ _ ι _ I hI c s hs m
  by_cases hm : ∀ k, 0 ≤ m k
  · obtain ⟨n, rfl⟩ : ∃ n : K → ℕ, m = fun k => (n k : ℤ) :=
      ⟨fun k => (m k).toNat, funext fun k => (Int.toNat_of_nonneg (hm k)).symm⟩
    have key := finrank_eq h1 hI hs n
    rw [(h1 F K ι I n).2, (h1 F K ι (I ⊔ Ideal.span {s}) n).2, key]
    by_cases hc : c ≤ n
    · rw [if_pos hc]
      have hnc : ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = fun k => ((n - c) k : ℤ) :=
        funext fun k => by
          have : c k ≤ n k := hc k
          simp only [Pi.sub_apply]
          omega
      rw [hnc, (h1 F K ι _ (n - c)).2]
      push_cast
      ring
    · rw [if_neg hc]
      have hneg : hilbFn (I.colon (Ideal.span {s}))
          ((fun k => (n k : ℤ)) - fun k => (c k : ℤ)) = 0 := by
        rw [hilbFn, if_neg]
        intro hall
        apply hc
        intro k
        show c k ≤ n k
        have := hall k
        simp only [Pi.sub_apply] at this
        omega
      rw [hneg]
      push_cast
      ring
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (c k : ℤ)) k := by
      intro hall
      apply hm
      intro k
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    simp only [hilbFn, if_neg hm, if_neg hm', sub_zero]

theorem closed : HilbExactDivide.Statement.{u} :=
  proof GradedFinite.proof

end HilbExactDivide

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace RenameIntNum

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h k
      exact h (e k)

theorem eventualValue_comp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  have key : ∀ c, (∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c) ↔
      ∀ᶠ m in atTop, g m = c := by
    intro c
    rw [← (precompIso e).map_atTop, Filter.eventually_map]
    rfl
  unfold eventualValue
  by_cases hg : ∃ c, ∀ᶠ m in atTop, g m = c
  · have hf : ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      hg.imp fun c hc => (key c).2 hc
    rw [dif_pos hf, dif_pos hg]
    obtain ⟨m, h1, h2⟩ := (((key _).1 hf.choose_spec).and hg.choose_spec).exists
    exact h1.symm.trans h2
  · have hf : ¬ ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      fun ⟨c, hc⟩ => hg ⟨c, (key c).1 hc⟩
    rw [dif_neg hf, dif_neg hg]

theorem mixedDiff_comp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

theorem proof (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P n bs
  have hH : hilbFn (P.comap (rename σ)) = fun m => hilbFn P (m ∘ E.symm) :=
    funext fun m => h F S K' κ ι' E σ hσ P m
  unfold intNum
  rw [hH, mixedDiff_comp E.symm bs (hilbFn P),
    eventualValue_comp E.symm (mixedDiff (fun i => bs i ∘ E.symm) (hilbFn P))]

end RenameIntNum

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def extendAddHom {K K' : Type} (j : K ↪ K') : (K → ℕ) →+ (K' → ℕ) where
  toFun x := Function.extend j x 0
  map_zero' := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_add' x y := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem weight_mapDomain_blockWeight {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by
  have key : (Finsupp.weight (R := ℕ) (blockWeight ι')).comp
        (Finsupp.mapDomain.addMonoidHom (M := ℕ) g) =
      (extendAddHom j).comp (Finsupp.weight (R := ℕ) (blockWeight ι)) := by
    ext v
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Finsupp.weight_single,
      one_smul]
    show blockWeight ι' (g v) _ = Function.extend j (blockWeight ι v) 0 _
    rename_i k'
    simp only [blockWeight, hg v]
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      rw [j.injective.extend_apply]
      by_cases hav : a = v.1
      · subst hav; simp
      · rw [Pi.single_eq_of_ne (fun e => hav (j.injective e)), Pi.single_eq_of_ne hav]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun e => h ⟨v.1, e.symm⟩)]
      rfl
  exact DFunLike.congr_fun key u

theorem RenameMultiHomog.proof : RenameMultiHomog.Statement.{u} := by
  intro R _ K K' _ _ j ι ι' g hg f d hf e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero g f e he
  rw [weight_mapDomain_blockWeight j ι ι' g hg u, hf hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

