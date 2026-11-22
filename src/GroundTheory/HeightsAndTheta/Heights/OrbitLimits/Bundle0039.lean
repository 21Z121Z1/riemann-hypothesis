import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0134
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenFibreChartDeg.isMultiHomogIdeal_ker_rat {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩

theorem GenFibreChartDeg.proof (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add, map_add]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PVarIntGraph
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Matrix Filter Topology
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartInt chartDens chartAbsDens sheetSum IsSheetAt)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet fibre IsFiniteProjection projHom pullback linPoly)

namespace VarIntGraph

variable {n e : ℕ}

def graphProj (A : Matrix (Fin e) (Fin n) ℂ) : Matrix (Fin e) (Fin (n + 1)) ℂ :=
  Matrix.of fun i => Fin.snoc (α := fun _ => ℂ) (A i) 0

theorem graphProj_mulVec (A : Matrix (Fin e) (Fin n) ℂ) (z : Fin (n + 1) → ℂ) :
    graphProj A *ᵥ z = A *ᵥ Fin.init z := by
  funext i
  simp [graphProj, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem graphProj_mulVec_graphPt (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    graphProj A *ᵥ graphPt p x = A *ᵥ x := by
  rw [graphProj_mulVec, graphPt_init]

theorem graphPt_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (graphPt p) := fun x x' h => by
  rw [← graphPt_init p x, ← graphPt_init p x', h]

theorem differentiable_eval (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ fun x : Fin n → ℂ => eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (differentiable_apply i)

theorem differentiable_graphPt (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (graphPt p) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [graphPt] using differentiable_eval p
  · simpa [graphPt] using differentiable_apply (𝕜 := ℂ) j

theorem differentiable_init : Differentiable ℂ fun z : Fin (n + 1) → ℂ => Fin.init z :=
  differentiable_pi.2 fun i => differentiable_apply (Fin.castSucc i)

theorem graphHom_comp_pullback (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) :
    (graphHom p).comp (pullback (graphProj A)) = pullback A := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [pullback, linPoly, graphProj, Fin.sum_univ_castSucc, graphHom_X_castSucc, MvPolynomial.algebraMap_eq]

theorem exists_quotEquiv (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ∃ φ : (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) ≃+* (MvPolynomial (Fin n) ℂ ⧸ J),
      ∀ q, φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk J (graphHom p q) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg), fun q => rfl⟩

theorem isFiniteProjection_graphProj {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    (p : MvPolynomial (Fin n) ℂ) (hA : IsFiniteProjection J A) :
    IsFiniteProjection (graphIdeal J p) (graphProj A) := by
  obtain ⟨φ, hφ⟩ := exists_quotEquiv J p
  have hcomp : ∀ q, φ (projHom (graphIdeal J p) (graphProj A) q) = projHom J A q := by
    intro q
    simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hφ]
    rw [← AlgHom.comp_apply, graphHom_comp_pullback]
  have heq : (projHom (graphIdeal J p) (graphProj A)).toRingHom =
      (φ.symm : (MvPolynomial (Fin n) ℂ ⧸ J) →+* _).comp (projHom J A).toRingHom :=
    RingHom.ext fun q => by simp [← hcomp]
  refine ⟨fun a b h => hA.injective (by rw [← hcomp, ← hcomp, h]), ?_⟩
  rw [heq]
  exact (RingHom.Finite.of_surjective _ φ.symm.surjective).comp hA.finite

theorem fibre_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (y : Fin e → ℂ) :
    fibre (graphIdeal J p) (graphProj A) y = graphPt p '' fibre J A y := by
  ext z
  constructor
  · rintro ⟨hz, hzy⟩
    refine ⟨Fin.init z, ⟨init_mem_zeroSet p hz, ?_⟩, graphPt_init_of_mem_zeroSet p hz⟩
    rwa [graphProj_mulVec] at hzy
  · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
    exact ⟨graphPt_mem_zeroSet p hx, by rw [graphProj_mulVec_graphPt]; exact hxy⟩

theorem isSheetAt_graph {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) (graphPt p ∘ s) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  refine ⟨U, hU, by rwa [graphProj_mulVec_graphPt], (differentiable_graphPt p).comp_differentiableOn hsd,
    by rw [graphProj_mulVec_graphPt, Function.comp_apply, hsx], fun y hy => ⟨?_, graphPt_mem_zeroSet p (hsZ y hy).2⟩,
    (fun z => Fin.init z) ⁻¹' V, ?_, ?_⟩
  · rw [Function.comp_apply, graphProj_mulVec_graphPt, (hsZ y hy).1]
  · exact differentiable_init.continuous.continuousAt.preimage_mem_nhds (by rwa [graphPt_init])
  · rintro z ⟨hz, hzV⟩ hzU
    rw [graphProj_mulVec] at hzU ⊢
    have h := hsV (Fin.init z) ⟨init_mem_zeroSet p hz, hzV⟩ hzU
    rw [Function.comp_apply, ← h, graphPt_init_of_mem_zeroSet p hz]

theorem isSheetAt_init {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin (n + 1) → ℂ}
    (hs : IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) :
    IsSheetAt J A x (fun y => Fin.init (s y)) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  rw [graphProj_mulVec_graphPt] at hxU hsx
  refine ⟨U, hU, hxU, differentiable_init.comp_differentiableOn hsd,
    by show Fin.init (s (A *ᵥ x)) = x; rw [hsx, graphPt_init],
    fun y hy => ⟨?_, init_mem_zeroSet p (hsZ y hy).2⟩, graphPt p ⁻¹' V,
    (differentiable_graphPt p).continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  · have h := (hsZ y hy).1
    rwa [graphProj_mulVec] at h
  · rintro x' ⟨hx', hx'V⟩ hx'U
    have h := hsV (graphPt p x') ⟨graphPt_mem_zeroSet p hx', hx'V⟩ (by rwa [graphProj_mulVec_graphPt])
    rw [graphProj_mulVec_graphPt] at h
    show x' = Fin.init (s (A *ᵥ x'))
    rw [← h, graphPt_init]

theorem sheet_eventuallyEq {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {z : Fin m → ℂ} {s t : (Fin e → ℂ) → Fin m → ℂ} (hs : IsSheetAt K B z s) (ht : IsSheetAt K B z t) :
    s =ᶠ[𝓝 (B *ᵥ z)] t := by
  obtain ⟨U, hU, hzU, hsd, hsz, hsZ, -⟩ := hs
  obtain ⟨U', hU', hzU', -, -, -, V, hV, htV⟩ := ht
  have hc : ContinuousAt s (B *ᵥ z) := (hsd.differentiableAt (hU.mem_nhds hzU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (B *ᵥ z), s y ∈ V := hc.preimage_mem_nhds (by rwa [hsz])
  filter_upwards [hU.mem_nhds hzU, hU'.mem_nhds hzU', hV'] with y hy hy' hyV
  obtain ⟨hBy, hZy⟩ := hsZ y hy
  have h := htV (s y) ⟨hZy, hyV⟩ (by rwa [hBy])
  rwa [hBy] at h

theorem maDens_congr_sheet {m : ℕ} (φ : Fin e → (Fin m → ℂ) → ℝ) {s t : (Fin e → ℂ) → Fin m → ℂ}
    {y : Fin e → ℂ} (h : s =ᶠ[𝓝 y] t) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y = ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ t) y := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ s) y) = fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ t) y :=
    funext fun k => ReciprocityTheory.AnForm.A.hessC_congr' (h.fun_comp (φ k))
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem sheetSum_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (G : ℝ → ℝ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin e → ℂ) :
    sheetSum (graphIdeal J p) (graphProj A)
        (fun z s => G (F z * ReciprocityTheory.AnForm.maDens (fun k => Φ k ∘ s) y)) y =
      sheetSum J A (fun x s => G (F (graphPt p x) *
        ReciprocityTheory.AnForm.maDens (fun k => (fun x => Φ k (graphPt p x)) ∘ s) y)) y := by
  unfold sheetSum
  rw [fibre_graphProj, finsum_mem_image (graphPt_injective p).injOn]
  refine finsum_mem_congr rfl fun x hx => ?_
  have hiff : (∃ s, IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) ↔ ∃ s, IsSheetAt J A x s :=
    ⟨fun ⟨_, h⟩ => ⟨_, isSheetAt_init h⟩, fun ⟨_, h⟩ => ⟨_, isSheetAt_graph h⟩⟩
  by_cases h : ∃ s, IsSheetAt J A x s
  · rw [dif_pos (hiff.2 h), dif_pos h]
    have hE := sheet_eventuallyEq (hiff.2 h).choose_spec (isSheetAt_graph (p := p) h.choose_spec)
    rw [graphProj_mulVec_graphPt, hx.2] at hE
    dsimp only
    rw [maDens_congr_sheet Φ hE]
    rfl
  · rw [dif_neg (mt hiff.1 h), dif_neg h]

theorem chartDens_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ) :
    chartDens (graphIdeal J p) (graphProj A) F Φ =
      chartDens J A (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x)) :=
  funext fun y => sheetSum_graphProj J A p id F Φ y

theorem chartAbsDens_congr_zeroSet {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {f g : (Fin m → ℂ) → ℝ} (h : ∀ x ∈ zeroSet K, f x = g x) (φ : Fin e → (Fin m → ℂ) → ℝ) :
    chartAbsDens K B f φ = chartAbsDens K B g φ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]

end VarIntGraph

open VarIntGraph in

theorem VarIntGraphInt.proof (hI : IntegralIndep.Statement) : VarIntGraphInt.Statement := by
  classical
  intro n e J p F Φ hJ hF hΦ hint
  have hG := graphIdeal_isPrime hJ p
  have hex : (∃ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B) ↔
      ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A := by
    refine ⟨fun ⟨B, hB⟩ => ?_, fun ⟨A, hA⟩ => ⟨_, isFiniteProjection_graphProj p hA⟩⟩
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
    rw [ringKrullDim_graphIdeal] at hd
    exact ComplexSets.LinearNoetherNormalization.proof n e J hd
  unfold varInt
  by_cases hJA : ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · rw [dif_neg (mt hex.1 hJA), dif_neg hJA]
  rw [dif_pos (hex.2 hJA), dif_pos hJA, chartInt, chartInt, ← chartDens_graphProj]
  have hA := isFiniteProjection_graphProj p hJA.choose_spec
  have hB := (hex.2 hJA).choose_spec
  obtain ⟨U, hU, hZU, hFU⟩ := hF
  have hFF : ∀ z ∈ zeroSet (graphIdeal J p), U.indicator F z = F z := fun z hz => Set.indicator_of_mem (hZU hz) F
  have hFm : Measurable (U.indicator F) := by
    rw [← Set.piecewise_eq_indicator]
    exact hFU.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
  have hi : Integrable (chartAbsDens (graphIdeal J p) (graphProj hJA.choose) (U.indicator F) Φ) := by
    rw [chartAbsDens_congr_zeroSet hFF]
    exact hint _ hA
  have h := (hI (n + 1) e (graphIdeal J p) _ _ (U.indicator F) Φ hG hd hA hB hFm hΦ hi).2
  rw [chartInt, chartInt, CutOffDominated.chartDens_congr_zeroSet hFF Φ,
    CutOffDominated.chartDens_congr_zeroSet hFF Φ] at h
  exact h.symm

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRankTransfer
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRankTransfer.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsClosed V → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ x ∈ projFullRank R BV, ∃ y ∈ connectedComponent x, y ∈ projMaxRank R Ψ BV

end GroundTheory.Heights₂.Heights.Targets
end
end

