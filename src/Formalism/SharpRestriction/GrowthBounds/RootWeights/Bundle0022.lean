import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0020
import Formalism.SharpRestriction.GrowthBounds.RootWeights.CommutatorTripleProductLeibniz
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0017
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0019
import Lemmata.ClearingDenominators.UmonLeUzmon
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SubstitutionPreservesOfGenerators
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0012
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0015
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0021
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DenominatorLemmaWithoutProjector
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem degreeZeroWeightsBounded_ellOf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (ellOf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hsplit : ν a + ∑ i ∈ Finset.univ.erase a, ν i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]; exact hsum
  have hell : (0 : ℤ) ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by positivity
  rw [abs_le]
  constructor
  · by_cases h0 : 0 ≤ ν a
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbpos⟩ : ∃ b ∈ Finset.univ.erase a, 0 < ν b := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonpos hc
        linarith
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have := weight_difference_le_ell_of_rep hE ν hne b a hba (by linarith)
      linarith
  · by_cases h0 : ν a ≤ 0
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbneg⟩ : ∃ b ∈ Finset.univ.erase a, ν b < 0 := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonneg hc
        linarith
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      have := weight_difference_le_ell_of_rep hE ν hne a b hab (by linarith)
      linarith

private theorem degreeZeroWeightsBounded_linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (linf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hmem : (ν a).natAbs ∈ {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} :=
    ⟨ν, by simpa [wtsOf] using hne, hsum, a, rfl⟩
  have hbdd : BddAbove {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} := by
    refine ⟨ellOf E (⊤ : Submodule K V), ?_⟩
    rintro k ⟨nu, hnu, hs, b, rfl⟩
    have hne' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    have h := degreeZeroWeightsBounded_ellOf hE nu hs hne' b
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hle : (ν a).natAbs ≤ linf E (⊤ : Submodule K V) := by
    unfold linf
    exact le_csSup hbdd hmem
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

theorem linf_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantDenominatorLinftyBound := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_linf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

theorem denominator_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionDenominator := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_ellOf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsScalarMultipleMemDelta
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem delta_le_nabla {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hK : v ∈ Nabla (O := O) E lam v) : Delta (O := O) E v ≤ NablaSub (O := O) E lam v := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u', hu', rfl⟩ u hu
  have := hK (u * u') (Submonoid.mul_mem _ hu hu')
  simpa using this

theorem integral_enveloping_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ UZmon E, x = u v} = ⊤ := by
  rw [eq_top_iff, ← hI.2.2.2]
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, enveloping_le_integral_enveloping E hu, rfl⟩

theorem nabla_to_delta_maps_fg [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam)
    (hK : v ∈ Nabla (O := O) E lam v) : (nablaToDeltaMaps (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := Module.End (KK O) V) _
    {φ | ∃ u ∈ UZmon E, ∃ u' ∈ UZmon E, φ = (xi ∘ₗ u) ∘ₗ LinearMap.applyₗ (u' v)} ?_ ?_
  · intro f hf
    have hz : ∀ u' ∈ UZmon E, f (u' v) = 0 := by
      intro u' hu'
      refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
      have := hf _ ⟨u, hu, u', hu', rfl⟩
      simpa using this
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← integral_enveloping_span_top hI]
      refine Submodule.span_le.2 ?_
      rintro x ⟨u, hu, rfl⟩
      exact hz u hu
    exact LinearMap.ext fun x => hk Submodule.mem_top
  · rintro φ ⟨u, hu, u', hu', rfl⟩ f hf
    have ha : u' v ∈ Nabla (O := O) E lam v := delta_le_nabla hK (Submodule.subset_span ⟨u', hu', rfl⟩)
    have hb : f (u' v) ∈ Nabla (O := O) E lam v := delta_le_nabla hK (hf _ ha)
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hb u hu
    exact ⟨c, by simpa using hc⟩

theorem nabla_finitely_generated [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    (NablaSub (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := V) _ {φ | ∃ u ∈ UZmon E, φ = xi ∘ₗ u} ?_ ?_
  · intro x hx
    refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
    have := hx _ ⟨u, hu, rfl⟩
    simpa using this
  · rintro φ ⟨u, hu, rfl⟩ x hx
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx u hu
    exact ⟨c, by simpa using hc⟩

theorem exists_scalar_multiple_mem_delta {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) (y : V) :
    ∃ o : O, o ≠ 0 ∧ o • y ∈ Delta (O := O) E v := by
  first | exact Bl.ClearingDenominators.goal1 .. | (apply Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply @Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> first | assumption | infer_instance)

theorem nabla_to_delta_maps_span_top [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hfg : (NablaSub (O := O) E lam v).FG) : MQ (K := KK O) (nablaToDeltaMaps (O := O) E lam v) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨G, hG⟩ := hfg
  choose o ho ho' using exists_scalar_multiple_mem_delta (O := O) hI
  set c : O := ∏ g ∈ G, o (f g) with hc
  have hc0 : c ≠ 0 := prod_ne_zero_iff.2 fun g _ => ho _
  have hmem : c • f ∈ nablaToDeltaMaps (O := O) E lam v := by
    intro x hx
    have hx' : x ∈ Submodule.span O (G : Set V) := hG ▸ hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem g hg =>
      rw [LinearMap.smul_apply, hc, ← mul_prod_erase G _ hg, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ho' _)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy
  have hc1 : algebraMap O (KK O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hc0
  have : f = (algebraMap O (KK O) c)⁻¹ • (c • f) := by
    rw [← algebraMap_smul (KK O) c f, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem coordinate_rank_one_mem_maps {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    xi.smulRight v ∈ nablaToDeltaMaps (O := O) E lam v := by
  intro x hx
  obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx 1 (Submonoid.one_mem _)
  rw [Module.End.one_apply] at hc
  rw [LinearMap.smulRight_apply, hc, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaOfInterfaces
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem genericMatrixInverse_eq_adjugate (R : Type*) [CommRing R] (n : ℕ) :
    genericMatrixInverse R n = (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) •
      ((genMat R n).adjugate.map (algebraMap _ (GLCoord R n))) := by
  ext i j
  simp [genericMatrixInverse, Matrix.smul_apply]

theorem genericMatrixInverse_mul (R : Type*) [CommRing R] (n : ℕ) : genericMatrixInverse R n * genericMatrixRootWeights R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.smul_mul, ← Matrix.map_mul, Matrix.adjugate_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

theorem genericMatrix_mul_inverse (R : Type*) [CommRing R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

section asm

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)

theorem generated_submodule_stable (G : MvPolynomial (ι × Fin n) R) (g : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R)
    (hg : g ∈ polUZgens R LL S) : ∀ x ∈ polGenSub R LL S G, g x ∈ polGenSub R LL S G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨g * u, Submonoid.mul_mem _ (Submonoid.subset_closure hg) hu, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem self_mem_generated_submodule (G : MvPolynomial (ι × Fin n) R) : G ∈ polGenSub R LL S G := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

theorem generic_translate_weights_mem (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (G : MvPolynomial (ι × Fin n) R) :
    ∀ m ∈ (genericTranslate LL S G).support, wtS LL S m ∈ polWts LL S (polGenSub R LL S G) := by
  classical
  set W := polGenSub R LL S G with hWdef
  have hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W := fun a k x hx =>
    generated_submodule_stable LL S G (binomPol R LL S a k) (Or.inr ⟨a, k, rfl⟩) x hx
  have hWd : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W := fun a b k hab x hx =>
    generated_submodule_stable LL S G (divPow R LL S a b k) (Or.inl ⟨a, b, k, hab, rfl⟩) x hx
  haveI hdom : IsDomain (GLCoord R n) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Matrix.det_mvPolynomialX_ne_zero (Fin n) R : (genMat R n).det ≠ 0))
  let K := FractionRing (GLCoord R n)
  let ψ : GLCoord R n →+* K := algebraMap (GLCoord R n) K
  have hψ : Function.Injective ψ := IsFractionRing.injective (GLCoord R n) K
  let φ : R →+* K := ψ.comp (coefficientMap R n)
  have good_of : ∀ h h' : Matrix (Fin n) (Fin n) K,
      (∀ w ∈ W, matrixSubst LL S φ h h' w ∈ scalarExtension φ W) → SubstitutionPreservesExtension LL S φ W h h' := by
    intro h h' hw
    unfold SubstitutionPreservesExtension
    intro x hx
    rw [scalarExtension] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      rw [matrixSubst_map]
      exact hw w hwW
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, RingHom.id_apply, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ c hy
  have good_mul : ∀ h1 h1' h2 h2' : Matrix (Fin n) (Fin n) K, SubstitutionPreservesExtension LL S φ W h1 h1' →
      SubstitutionPreservesExtension LL S φ W h2 h2' → SubstitutionPreservesExtension LL S φ W (h1 * h2) (h2' * h1') := by
    intro h1 h1' h2 h2' g1 g2
    unfold SubstitutionPreservesExtension at g1 g2 ⊢
    intro x hx
    rw [← matrixSubst_comp]
    exact g1 _ (g2 x hx)
  have good_tr : ∀ (a b : Fin n), a ≠ b → ∀ t : K,
      SubstitutionPreservesExtension LL S φ W (Matrix.transvection a b t) (Matrix.transvection a b (-t)) := by
    intro a b hab t
    apply good_of
    intro w hw
    rw [hT R K ι LL n S φ a b hab t w (w.totalDegree + 1) (Nat.lt_succ_self _)]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hWd a b k hab w hw, rfl⟩)
  have good_diag : ∀ u : Fin n → Kˣ, SubstitutionPreservesExtension LL S φ W (Matrix.diagonal fun a => ((u a : Kˣ) : K))
      (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) := by
    intro u
    apply good_of
    intro w hw
    rw [MvPolynomial.as_sum w, map_sum]
    have hmono : ∀ m ∈ w.support, matrixSubst LL S φ (Matrix.diagonal fun a => ((u a : Kˣ) : K))
        (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) (MvPolynomial.monomial m (w.coeff m)) =
        (((∏ a, u a ^ (wtS LL S m a) : Kˣ) : K)) • MvPolynomial.map φ (MvPolynomial.monomial m (w.coeff m)) := by
      intro m _
      rw [hTo R K ι LL n S φ u m (w.coeff m), MvPolynomial.map_monomial, MvPolynomial.smul_monomial,
        smul_eq_mul]
      congr 1
      exact mul_comm _ _
    rw [Finset.sum_congr rfl hmono,
      ← Finset.sum_fiberwise_of_maps_to (g := fun m => wtS LL S m) (t := w.support.image (fun m => wtS LL S m))
        (fun m hm => Finset.mem_image_of_mem _ hm)]
    refine Submodule.sum_mem _ fun ν _ => ?_
    convert Submodule.smul_mem _ (((∏ a, u a ^ (ν a) : Kˣ) : K))
      (show MvPolynomial.map φ (weightComponent LL S ν w) ∈ scalarExtension φ W by
        rw [scalarExtension]
        exact Submodule.subset_span ⟨_, hGr R ι LL n S W hW2 w hw ν, rfl⟩) using 1
    unfold weightComponent
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr ?_ fun m hm => ?_
    · ext m
      simp
    · rw [(Finset.mem_filter.mp hm).2]
  have good_list : ∀ l : List (Matrix.TransvectionStruct (Fin n) K),
      SubstitutionPreservesExtension LL S φ W (l.map Matrix.TransvectionStruct.toMatrix).prod
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod ∧
      (l.map Matrix.TransvectionStruct.toMatrix).prod *
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = 1 ∧
      (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod *
        (l.map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.reverse_nil]
      refine ⟨?_, mul_one 1, mul_one 1⟩
      unfold SubstitutionPreservesExtension
      intro x hx
      rw [matrixSubst_one, MvPolynomial.map_id]
      exact hx
    | cons t l ih =>
      obtain ⟨hg, h1, h2⟩ := ih
      have ht1 : t.toMatrix * Matrix.transvection t.i t.j (-t.c) = 1 := by
        exact t.mul_inv
      have ht2 : Matrix.transvection t.i t.j (-t.c) * t.toMatrix = 1 := by
        exact t.inv_mul
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      generalize (l.map Matrix.TransvectionStruct.toMatrix).prod = P at hg h1 h2 ⊢
      generalize (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P' at hg h1 h2 ⊢
      refine ⟨good_mul _ _ _ _ (good_tr t.i t.j t.hij t.c) hg, ?_, ?_⟩
      · rw [mul_assoc, ← mul_assoc P, h1, one_mul, ht1]
      · rw [mul_assoc, ← mul_assoc (Matrix.transvection t.i t.j (-t.c)), ht2, one_mul, h2]
  set A : Matrix (Fin n) (Fin n) K := (genericMatrixInverse R n).map ψ with hAdef
  set A' : Matrix (Fin n) (Fin n) K := (genericMatrixRootWeights R n).map ψ with hA'def
  have hAA' : A * A' = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrixInverse_mul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hA'A : A' * A = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrix_mul_inverse, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  obtain ⟨l1, l2, D, hAdec⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  obtain ⟨g1, e1, f1⟩ := good_list l1
  obtain ⟨g2, e2, f2⟩ := good_list l2
  generalize (l1.map Matrix.TransvectionStruct.toMatrix).prod = P1 at hAdec g1 e1 f1
  generalize (l1.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P1' at g1 e1 f1
  generalize (l2.map Matrix.TransvectionStruct.toMatrix).prod = P2 at hAdec g2 e2 f2
  generalize (l2.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P2' at g2 e2 f2
  have hdiag : Matrix.diagonal D = P1' * A * P2' := by
    rw [hAdec, ← mul_assoc, ← mul_assoc, f1, one_mul, mul_assoc, e2, mul_one]
  have hDinv : Matrix.diagonal D * (P2 * A' * P1) = 1 := by
    rw [hdiag]
    simp only [mul_assoc]
    rw [← mul_assoc P2' P2, f2, one_mul, ← mul_assoc A A', hAA', one_mul, f1]
  have hD0 : ∀ a, D a ≠ 0 := by
    intro a h0
    have h3 := congrFun (congrFun hDinv a) a
    rw [Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h3
    exact zero_ne_one h3
  let u : Fin n → Kˣ := fun a => Units.mk0 (D a) (hD0 a)
  have gd := good_diag u
  have hu1 : (Matrix.diagonal fun a => ((u a : Kˣ) : K)) = Matrix.diagonal D := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  have hu2 : (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) = Matrix.diagonal fun a => (D a)⁻¹ := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  rw [hu1, hu2] at gd
  have gA := good_mul _ _ _ _ (good_mul _ _ _ _ g1 gd) g2
  have hX : P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1') = A' := by
    have hdd : Matrix.diagonal D * Matrix.diagonal (fun a => (D a)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hD0 a)
    have hAX : A * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) = 1 := by
      rw [hAdec]
      simp only [mul_assoc]
      rw [← mul_assoc P2 P2', e2, one_mul, ← mul_assoc (Matrix.diagonal D), hdd, one_mul, e1]
    calc P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')
        = (A' * A) * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) := by rw [hA'A, one_mul]
      _ = A' := by rw [mul_assoc, hAX, mul_one]
  rw [← hAdec, hX] at gA
  have hGW : MvPolynomial.map φ G ∈ scalarExtension φ W := Submodule.subset_span ⟨G, self_mem_generated_submodule LL S G, rfl⟩
  have hHK : MvPolynomial.map ψ (genericTranslate LL S G) ∈ scalarExtension φ W := by
    rw [genericTranslate, map_matrixSubst, ← hAdef, ← hA'def, ← matrixSubst_map]
    exact gA _ hGW
  intro m hm
  have hsupp : m ∈ (MvPolynomial.map ψ (genericTranslate LL S G)).support := by
    rwa [MvPolynomial.support_map_of_injective _ hψ]
  exact scalarExtension_monomial_weights (LL := LL) (S := S) (φ := φ) (W := W) hGr hW2 _ hHK m hsupp

end asm

theorem generated_module_weight_lemma_of_interfaces (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (hSt : TwistExponentsAreWeightEntries) (hSp : GenericMonomialsSpecialise) :
    GeneratedModuleWeightDescription := by
  intro R _ ι _ LL n _ S
  refine ⟨fun G θ => ?_, fun G M => ?_⟩
  · rw [valS, hSt R ι LL n S (lastIdx n) G, Finset.le_inf_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := lastIdx n) (Pr := fun z => θ ≤ z) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this
  · rw [lam1S, hSt R ι LL n S 0 G, Finset.sup_le_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := 0) (Pr := fun z => z ≤ M) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolynomialsEnvelopingStable
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem integral_polynomials_enveloping_stable (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι) :
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
      ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
        InBB (O := O) p F → InBB (O := O) p (u F) :=
  ((integral_formula_lattice_holds p n' O S0 hG).2 n ι LL).1 S

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
end
end

