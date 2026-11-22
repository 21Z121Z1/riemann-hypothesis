import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSublattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights

noncomputable section

theorem gramDet_sub {K : Type*} [Field K] [NumberField K] (M : HermitianBundle K)
    (F : Submodule (𝓞 K) M.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) :
    gramDet (M.sub F).metric σ s = gramDet M.metric σ (fun i ↦ (s i : M.carrier)) := by
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec (M.sub F).metric σ (s i)) =
      Matrix.gram ℂ fun i ↦ fibreVec M.metric σ (s i : M.carrier) := by
    ext i j
    rfl
  simp only [gramDet]
  rw [hG]

theorem card_quotient_span_sub {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E]
    [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) {ι : Type*} (s : ι → F) :
    Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) * Nat.card (E ⧸ F) := by
  set S := Submodule.span (𝓞 K) (Set.range s)
  set T := Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))
  have hspan : T = S.map F.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hTF : T ≤ F := by
    rw [hspan]; exact Submodule.map_subtype_le F S
  rw [← Submodule.card_quotient_mul_card_quotient F T hTF]
  congr 1
  have hk : LinearMap.ker (T.mkQ ∘ₗ F.subtype) = S := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hspan,
      Submodule.comap_map_eq_of_injective F.injective_subtype]
  have hr : LinearMap.range (T.mkQ ∘ₗ F.subtype) = F.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hk, ← hr]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem Sublattice.proof : Sublattice.Statement := by
  intro K _ _ M F hF
  have : Module.Finite (𝓞 K) F := inferInstanceAs (Module.Finite (𝓞 K) (M.sub F).carrier)
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := F)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ (s i : M.carrier)) :=
    hs.map' F.subtype (LinearMap.ker_eq_bot.mpr F.injective_subtype)
  have hcardF : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) F :=
    Fintype.card_fin _
  have hcardM : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) M.carrier := by
    rw [Fintype.card_fin, hF]
  have hdM : M.arithDegree = degreeWith M.metric (fun i ↦ (s i : M.carrier)) :=
    arithDegree_eq _ ht hcardM
  have hdF : (M.sub F).arithDegree = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ (fun i ↦ (s i : M.carrier))) := by
    have h1 := arithDegree_eq (M.sub F).metric hs hcardF
    rw [HermitianBundle.arithDegree, h1]
    unfold degreeWith
    simp only [gramDet_sub]
    rfl
  have hfin := finite_quotient_span ht hcardM
  have hpos : 0 < Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : M.carrier))) :=
    Nat.card_pos
  have hc := card_quotient_span_sub F s
  rw [hc] at hpos
  have ha : (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have hb : (0 : ℝ) < Nat.card (M.carrier ⧸ F) := by
    exact_mod_cast Nat.pos_of_mul_pos_left hpos
  have hsum : M.arithDegree = (M.sub F).arithDegree + Real.log (Nat.card (M.carrier ⧸ F)) := by
    rw [hdM, hdF, degreeWith, hc, Nat.cast_mul, Real.log_mul ha.ne' hb.ne']
    ring
  have hlog : 0 ≤ Real.log (Nat.card (M.carrier ⧸ F)) := Real.log_natCast_nonneg _
  have hdeg : M.deg = (M.sub F).deg + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K := by
    simp only [HermitianBundle.deg]
    rw [hsum, add_div]
  refine ⟨hdeg, ?_⟩
  rw [hdeg]
  exact le_add_of_nonneg_right (div_nonneg hlog (Nat.cast_nonneg _))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

section Scale

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def localScalar (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) : v.adicCompletion K :=
  (algebraMap (𝓞 K) (v.adicCompletionIntegers K) b : v.adicCompletion K)

theorem localScalar_eq (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    localScalar v b = FinitePlace.embedding v (b : K) := rfl

theorem localScalar_ne_zero (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    localScalar v b ≠ 0 := by
  rw [localScalar_eq]
  exact (map_ne_zero _).mpr (by exact_mod_cast hb)

def localSmul (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) :=
  LinearEquiv.smulOfNeZero _ _ (localScalar v b) (localScalar_ne_zero v hb)

theorem toLocal_smul_eq (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) (x : V) :
    toLocal v (b • x) = localScalar v b • toLocal v x := by
  rw [← algebraMap_smul K b x, map_smul,
    ← algebraMap_smul (v.adicCompletion K) (algebraMap (𝓞 K) K b) (toLocal v x)]
  rfl

def smulSub (b : 𝓞 K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L.map (b • LinearMap.id)

theorem mem_smulSub_of_mem (b : 𝓞 K) {L : Submodule (𝓞 K) V} {x : V} (hx : x ∈ L) :
    b • x ∈ smulSub b L :=
  ⟨x, hx, rfl⟩

theorem smulSub_le (b : 𝓞 K) (L : Submodule (𝓞 K) V) : smulSub b L ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact L.smul_mem b hx

theorem localLattice_smulSub (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0)
    (L : Submodule (𝓞 K) V) :
    (localLattice v (smulSub b L) : Set (v.adicCompletion K ⊗[K] V)) =
      localSmul v hb '' localLattice v L := by
  set f := ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _).toLinearMap.restrictScalars
    (v.adicCompletionIntegers K))
  have h1 : toLocal v '' (smulSub b L : Set V) = f '' (toLocal v '' (L : Set V)) := by
    rw [Set.image_image]
    ext w
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [toLocal_smul_eq]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨b • x, mem_smulSub_of_mem b hx, ?_⟩
      rw [toLocal_smul_eq]
      rfl
  have h2 : localLattice v (smulSub b L) = (localLattice v L).map f := by
    rw [localLattice, localLattice, Submodule.map_span, h1]
  rw [h2, Submodule.map_coe]
  rfl

def scaledLattice (M : FullLattice K V) {b : 𝓞 K} (hb : b ≠ 0) : FullLattice K V where
  carrier := smulSub b M.carrier
  fg := M.fg.map _
  span_eq := by
    rw [eq_top_iff, ← M.span_eq, Submodule.span_le]
    intro x hx
    have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
    have : x = (b : K)⁻¹ • (b • x) := by
      rw [← algebraMap_smul K b x, smul_smul]
      simp [hb']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_smulSub_of_mem b hx))

end Scale

def LocalIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    M₂.carrier ≤ M₁.carrier →
    (∀ v, (localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' localLattice v M₁.carrier) →
      (Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) : ℝ) =
        ∏ᶠ v, ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖⁻¹

section Witness

variable (K : Type u) [Field K] [NumberField K]

theorem LocalIndex.witness :
    (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
        (FullLattice.standard K 2).carrier ∧
      ∀ v, (localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier :
          Set (v.adicCompletion K ⊗[K] (Fin 2 → K))) = localSmul v (two_ne_zero (α := 𝓞 K)) '' localLattice v (FullLattice.standard K 2).carrier :=
  ⟨smulSub_le _ _, fun v ↦ localLattice_smulSub v _ _⟩

example := LocalIndex.witness ℚ
example := LocalIndex.witness GaussianField

end Witness

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

