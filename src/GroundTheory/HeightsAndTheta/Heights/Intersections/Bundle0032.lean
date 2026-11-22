import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Weights

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def zDegInl : (K → ℕ) →+ (K ⊕ Unit → ℤ) :=
  AddMonoidHom.mk' (fun a x => Sum.elim (fun k => (a k : ℤ)) (fun _ => 0) x) (by
    intro a b
    funext x
    cases x <;> simp)

def zDeg : (K ⊕ Unit → ℕ) →+ (K ⊕ Unit → ℤ) := AddMonoidHom.compLeft (Nat.castAddMonoidHom ℤ) _

omit [Fintype K] [DecidableEq K] in
theorem zDeg_injective : Function.Injective (zDeg (K := K)) := fun a b h =>
  funext fun x => by
    have := congrFun h x
    simpa [zDeg] using this

variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)

def genericWeight : S ⊕ (Σ k, ι k) → (K ⊕ Unit → ℤ)
  | .inl s => Pi.single (Sum.inr ()) 1 - zDegInl (γ s)
  | .inr p => zDegInl (NumbersDVR.blockWeight ι p)

variable {ι} {N1 : ℕ}

def genericSubstitution (V : S → Fin N1 → MRing ι) : (Σ x, PBlk ι N1 x) → MvPolynomial (S ⊕ (Σ k, ι k)) ℤ
  | ⟨.inl k, i⟩ => X (.inr ⟨k, i⟩)
  | ⟨.inr _, j⟩ => ∑ s, rename Sum.inr (V s j) * X (.inl s)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genericSubstitution_isWeightedHomogeneous (V : S → Fin N1 → MRing ι)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    (v : Σ x, PBlk ι N1 x) :
    IsWeightedHomogeneous (genericWeight ι γ) (genericSubstitution V v) (zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) := by
  rcases v with ⟨k | u, i⟩
  · convert isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr ⟨k, i⟩) using 1
    · rfl
    · funext x
      cases x <;> simp [genericWeight, zDegInl, zDeg, NumbersDVR.blockWeight, Pi.single_apply]
  · have hdeg : zDeg (NumbersDVR.blockWeight (PBlk ι N1) ⟨Sum.inr u, i⟩) = Pi.single (Sum.inr ()) 1 := by
      funext x
      cases x <;> simp [zDeg, NumbersDVR.blockWeight]
    rw [hdeg]
    change Fin N1 at i
    refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
    have hren : IsWeightedHomogeneous (genericWeight ι γ) (rename Sum.inr (V s i) : MvPolynomial (S ⊕ _) ℤ)
        (zDegInl (γ s)) := by
      rw [rename_eq_aeval]
      refine isWeightedHomogeneous_aeval_of_weights (w := fun p => zDegInl (NumbersDVR.blockWeight ι p))
        (e := X ∘ Sum.inr)
        (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) ?_
      intro d hd
      rw [NumbersDVR.weight_comp_addMonoidHom, hV s i hd]
    convert hren.mul (isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inl s)) using 1
    show _ = zDegInl (γ s) + (Pi.single (Sum.inr ()) 1 - zDegInl (γ s))
    abel

end Weights

section Kernel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]

def genericEvaluation (P : Ideal (MRing ι)) : MvPolynomial (S ⊕ (Σ k, ι k)) ℤ →+* MvPolynomial S (FnField P) :=
  (map (toFn P)).comp (sumAlgEquiv ℤ S (Σ k, ι k)).toAlgHom.toRingHom

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem sumAlgEquiv_rename_inr (f : MRing ι) :
    sumAlgEquiv ℤ S (Σ k, ι k) (rename Sum.inr f) = C f := by
  have := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr ℤ S (Σ k, ι k)) f
  simpa [algebraMap_eq] using this

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem genericEvaluation_rename_inr (P : Ideal (MRing ι)) (f : MRing ι) :
    genericEvaluation (S := S) P (rename Sum.inr f) = C (toFn P f) := by
  simp [genericEvaluation, sumAlgEquiv_rename_inr]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genMap_eq_comp [DecidableEq K] (P : Ideal (MRing ι)) {N1 : ℕ} (V : S → Fin N1 → MRing ι) :
    genMap P (fun s j => toFn P (V s j)) = (genericEvaluation P).comp (aeval (genericSubstitution V)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
  rintro ⟨k | u, i⟩
  · simp [genMap, genericSubstitution, genericEvaluation, genPt, toFn]
  · change Fin N1 at i
    simp only [genMap, genericSubstitution, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X, map_sum, map_mul, genericEvaluation_rename_inr]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [genericEvaluation]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem ker_genericEvaluation_le (P : Ideal (MRing ι)) :
    RingHom.ker (genericEvaluation (S := S) P) ≤ Ideal.map (rename Sum.inr) P := by
  intro f hf
  set e := sumAlgEquiv ℤ S (Σ k, ι k)
  have hg : e f ∈ Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P := by
    rw [← ker_toFn P, ← MvPolynomial.ker_map]
    exact hf
  have hre : ∀ x : MRing ι, e.symm (C x) = rename Sum.inr x := by
    intro x
    rw [AlgEquiv.symm_apply_eq]
    exact (sumAlgEquiv_rename_inr x).symm
  have h1 : Ideal.map e.symm (Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P) ≤
      Ideal.map (rename Sum.inr) P := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, hre]
    exact Ideal.mem_map_of_mem _ hx
  simpa using h1 (Ideal.mem_map_of_mem e.symm hg)

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem map_le_ker_genericEvaluation (P : Ideal (MRing ι)) :
    Ideal.map (rename Sum.inr) P ≤ RingHom.ker (genericEvaluation (S := S) P) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, genericEvaluation_rename_inr]
  have h0 : toFn P x = 0 := by rw [← RingHom.mem_ker, ker_toFn]; exact hx
  rw [h0, map_zero]

theorem component_mem_ker_genMap [DecidableEq K] (P : Ideal (MRing ι)) (G : Set (MRing ι))
    (hG : ∀ f ∈ G, ∃ a, IsMultiHomog f a) (hPG : P = Ideal.span G) {N1 : ℕ}
    (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    {f : MRing (PBlk ι N1)} (hf : f ∈ RingHom.ker (genMap P fun s j => toFn P (V s j)))
    (b : K ⊕ Unit → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (PBlk ι N1)) b f ∈
      RingHom.ker (genMap P fun s j => toFn P (V s j)) := by
  classical
  rw [genMap_eq_comp] at hf ⊢
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at hf ⊢
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf ⊢
  have hJ := ker_genericEvaluation_le P hf
  have hGw : ∀ g ∈ G, ∃ a, IsWeightedHomogeneous (fun p => zDegInl (NumbersDVR.blockWeight ι p)) g a := by
    intro g hg
    obtain ⟨a, ha⟩ := hG g hg
    refine ⟨zDegInl a, fun d hd => ?_⟩
    rw [NumbersDVR.weight_comp_addMonoidHom, ((Bridge.isMultiHomog_iff g a).mpr ha) hd]
  rw [hPG, rename_eq_aeval] at hJ
  have hc := weightedHomogeneousComponent_mem_map_aeval (ω := genericWeight ι γ) (e := X ∘ Sum.inr)
    (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) G hGw hJ (zDeg b)
  rw [← rename_eq_aeval, ← hPG] at hc
  rw [← aeval_weightedHomogeneousComponent_of_weights
      (fun v => zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) (genericWeight ι γ) (genericSubstitution V)
      (genericSubstitution_isWeightedHomogeneous γ V hV), NumbersDVR.weightedHomogeneousComponent_comp_addMonoidHom zDeg zDeg_injective]
    at hc
  exact map_le_ker_genericEvaluation P hc

end Kernel

theorem ProjBundleMultiHomog.proof : ProjBundleMultiHomog.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hQ hB
  classical
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, -⟩ := hP
  have := hPp
  have hPc := (Bridge.isMultiHomogIdeal_iff P).mpr hPh
  obtain ⟨S, _, V, γ, hV, hVker, hBspan⟩ := exists_homog_span P hPc c m
    (fun r j => (Bridge.isMultiHomog_iff _ _).mpr (hQ.1 r j)) B
    (fun a => by rw [← hB.2]; exact Submodule.subset_span ⟨a, rfl⟩)
  have hker : projBundleIdeal P B = RingHom.ker (genMap P fun s j => toFn P (V s j)) :=
    le_antisymm (ker_genMap_le P B _ fun s => by rw [hB.2]; exact hVker s)
      (ker_genMap_le P _ B hBspan)
  rw [hker]
  obtain ⟨G, hG, hPG⟩ := hPh
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf b => component_mem_ker_genMap P G hG hPG V γ hV hf b

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PWWRatioBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem WWRatioBasis.proof (hM : MobiusAlgIndep.Statement) : WWRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF hxt hδ hδF hφ hgF hg ha
  obtain ⟨hden, hr⟩ := hM Ω Φ 2 a (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1)) ha
    (RatioField.det_ne_zero e b φ g (x i₀) hx k₀ k₁ hφ hg)
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  set W := T.wwCoord x δ e φ (a 0) (a 1)
  let c : ∀ k, T.wwIdx ι ν κ k := fun k => T.WBlk.casesOn (motive := fun k => T.wwIdx ι ν κ k) k i₀ l₀ k₀ k₀
  let r : Fin 2 → Φ := fun j => T.lineVal e (φ k₁) (a j) / T.lineVal e (φ k₀) (a j)
  let t' : Fin (d + 2) → Φ := fun n => Sum.elim (fun m => algebraMap Ω Φ (t m)) r (finSumFinEquiv.symm n)
  have ht'n : ∀ m, algebraMap Ω Φ (t m) ∈ Set.range t' := fun m =>
    ⟨finSumFinEquiv (Sum.inl m), by simp [t']⟩
  have hr' : ∀ j, r j ∈ Set.range t' := fun j => ⟨finSumFinEquiv (Sum.inr j), by simp [t']⟩
  have hrC : ∀ j, r j ∈ coneRatios W c := fun j => by
    fin_cases j
    exacts [⟨⟨.line0, k₁⟩, rfl⟩, ⟨⟨.line1, k₁⟩, rfl⟩]

  have hline : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ j k, T.lineVal e (φ k) (a j) / T.lineVal e (φ k₀) (a j) ∈ L := by
    intro L hF hrL j k
    have hgF' : ∀ k q, g k q ∈ F := hgF
    rw [RatioField.lineVal_cramer e b φ g (x i₀) k₀ k₁ k hφ hg, add_div, mul_div_assoc,
      mul_div_assoc, div_self (show T.lineVal e (φ k₀) (a j) ≠ 0 from hden j)]
    refine L.add_mem (L.mul_mem (hF _ ?_) (L.one_mem)) (L.mul_mem (hF _ ?_) (hrL j)) <;>
      exact F.div_mem (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))
        (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))

  have hcases : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ y ∈ coneRatios W c, y ∈ L := by
    rintro L hF hrL _ ⟨⟨blk, i⟩, rfl⟩
    cases blk
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (hδF i)
    · exact hline L hF hrL 0 i
    · exact hline L hF hrL 1 i
  refine ⟨c, t', fun k => ?_, ?_, fun n => ?_, fun y hy => ?_⟩
  · cases k
    exacts [(map_ne_zero _).mpr hx, (map_ne_zero _).mpr hδ, hden 0, hden 1]
  · have hti : AlgebraicIndependent ℚ fun m => algebraMap Ω Φ (t m) :=
      ht.map' (f := (algebraMap Ω Φ).toRatAlgHom) (algebraMap Ω Φ).injective
    refine (algebraicIndependent_equiv' (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)) ?_).mpr
      (hti.sumElim_of_tower (S := Ω) (by rintro _ ⟨m, rfl⟩; exact ⟨t m, rfl⟩) hr)
    funext n
    simp only [Function.comp, Equiv.trans_apply, t']
    cases finSumFinEquiv.symm n <;> rfl
  · have hbase : ∀ z ∈ F, algebraMap Ω Φ z ∈ IntermediateField.adjoin ℚ (coneRatios W c) :=
      fun z hz => RatioField.map_mem (S := Set.range fun j => x j / x i₀) (fun w hw => by
        obtain ⟨j, rfl⟩ := hw
        exact IntermediateField.subset_adjoin _ _ ⟨⟨.base, j⟩, by simp [W, c, T.wwCoord, map_div₀]⟩) hz
    obtain ⟨m | j, rfl⟩ := finSumFinEquiv.surjective n
    · simpa [t'] using hbase _ (htF m)
    · simpa [t'] using IntermediateField.subset_adjoin _ _ (hrC j)
  · have hL := hcases ((algebraicClosure (IntermediateField.adjoin ℚ (Set.range t')) Φ).restrictScalars ℚ)
      (fun z hz => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (RatioField.isAlgebraic_map_adjoin (S := Set.range fun j => x j / x i₀) ht
          (fun w hw => by obtain ⟨j, rfl⟩ := hw; exact hxt j) ht'n hz)))
      (fun j => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (isAlgebraic_algebraMap (⟨r j, IntermediateField.subset_adjoin _ _ (hr' j)⟩ :
          IntermediateField.adjoin ℚ (Set.range t'))))) y hy
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp hL)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagFormDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagFormDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (α : T.WBlk → ℕ) (d : MRing (T.wwIdx ι ν κ)), IsMultiHomog d α →
      d ∈ T.wwIdeal x δ e φ (a 0) (a 0) →
      ∃ (γ β : T.WBlk → ℕ) (s r : MRing (T.wwIdx ι ν κ)), IsMultiHomog s γ ∧ IsMultiHomog r β ∧
        (∀ k, α k + γ k + T.wwDeg 3 0 k = β k + T.wwDeg 0 1 k) ∧
        s ∉ T.wwIdeal x δ e φ (a 0) (a 0) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) d * aeval (T.wwCoord x δ e φ (a 0) (a 1)) s =
          T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) r

section Quot

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem DiagFormDiv.mem_diag_of_quot (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) {n : ℕ} {g h : MRing (T.wwIdx ι ν κ)}
    (hg : IsMultiHomog g (T.wwDeg n 1)) (hh : IsMultiHomog h (T.wwDeg (n + 3) 0))
    (hq : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) :
    g ∈ T.wwIdeal x δ e φ (a 0) (a 0) := by
  have key : ∀ b : Fin 2 → Φ, (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom)
      (DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
        C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k) =
      C (aeval (T.wwCoord x δ e φ (b 0) (b 1)) g - (b 1 - b 0) * aeval (T.wwCoord x δ e φ (b 0) (b 1)) h) *
        ((∏ k, X k ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) := by
    intro b
    have e1 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) g _ hg
    have e2 := DiagRAux.multiConeMap_of_homog (T.wwCoord x δ e φ (b 0) (b 1)) h _ hh
    rw [DiagonalOrder.multiConeMap_eq, RingHom.comp_apply] at e1 e2
    rw [map_sub, map_mul, map_mul, map_mul, e1, e2]
    simp only [map_prod, map_pow, map_X, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul, aeval_X]
    ring
  have hZ : DiagonalOrder.polyConeMap x δ e φ g * ∏ k, X k ^ T.wwDeg (n + 3) 0 k -
      C (X 1 - X 0) * DiagonalOrder.polyConeMap x δ e φ h * ∏ k, X k ^ T.wwDeg n 1 k = 0 := by
    apply MvPolynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.mp ha)
    rw [key a, hq, T.diagSec, sub_self, C_0, zero_mul, map_zero]
  have h0 := key (fun _ => a 0)
  rw [hZ, map_zero, sub_self, zero_mul, sub_zero] at h0
  have hm : ((∏ k, (X k : MvPolynomial T.WBlk Φ) ^ T.wwDeg n 1 k) * ∏ k, X k ^ T.wwDeg (n + 3) 0 k) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
  have hv : aeval (T.wwCoord x δ e φ (a 0) (a 0)) g = 0 :=
    C_eq_zero.1 ((mul_eq_zero.1 h0.symm).resolve_right hm)
  by_contra hn
  exact (DiagRAux.not_mem_ker_iff_aeval_ne _ g _ hg).1 hn hv

end Quot

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFIntZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι')
    (A : HermLine ι') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    arInt P' s A (Fin.append L' N) = 0

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFSecAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin (r + 1) → HermLine ι')
    (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + (r + 1)) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFSecRed.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFSecAt I r → PFAt I (r + 1)

section Inhabitants

def fibreLineDeg : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => 0) fun _ => 1

def fibreCoord : MRing PointLineBlocks := X ⟨Sum.inr (), (0 : Fin 2)⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.UniquenessDegreeFormOfIntersectionForm
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def ThmIUniquePosDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      1 ≤ n → IsArithVar P n → AllSmooth L → I P n L = J P n L

theorem IsFamily.isRFamily {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {I : Family ι}
    (h : IsFamily I) : IsRFamily I :=
  IsIntersectionFamily.isRFamily ((IsFamily.equiv I).1 h)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

