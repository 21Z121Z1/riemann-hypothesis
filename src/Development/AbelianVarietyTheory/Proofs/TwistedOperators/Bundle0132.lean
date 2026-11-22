import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix GlobalTheory.AdelicLatMove
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStab

variable {D : D7}

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  ext i j
  rfl

theorem mulVec_mem_of_mem_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (x : Fin n → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hM
  rw [hβ _]
  have hx' := (hβ x).1 hx
  have e : (β⁻¹).val * (frGL β y).val = (intGL D.host.F D.host.E n y).val * (β⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    change β⁻¹ * (β * intGL D.host.F D.host.E n y * β⁻¹) = _
    group
  intro i
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  change ∑ j, (intGL D.host.F D.host.E n y).val i j * ((β⁻¹).val *ᵥ x) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (y.val i j).2 (hx' j)

theorem rankOne_smul_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    (γ : Af D.host.F) (hγ : γ ∈ Formalism.UG.intAd D.host.F) (hP : ∀ v, ¬ Pv v → evalV D.host.F v γ = 0)
    (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → Lev.EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → Lev.EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • t) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s _ ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      have e : (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • fun i => (y i ⊗ₜ[D.host.F] β : Lev.EAf D)) =
          fun i => y i ⊗ₜ[D.host.F] (γ * β) := by
        ext i
        simp
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨γ * β * α, (mul_mem (mul_mem hγ hβ) hα : γ * β * α ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_,
        a, ha, x, hx, y, hy, rankOne_pure S T a x y α (γ * β)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [smul_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add, map_add]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (g : GA D S) (h : GA D T)
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : (fun i => (t i ⊗ₜ[D.host.F] α : Lev.EAf D)) =
        ((1 : D.host.E) ⊗ₜ[D.host.F] α : Lev.EAf D) • fun i => (t i ⊗ₜ[D.host.F] (1 : Af D.host.F) : Lev.EAf D) := by
      ext i
      simp
    rw [← e, actO_rankOne, e2, Matrix.mulVec_smul, ← finE_val, ← finE_val]
    exact rankOne_smul_mem_latO S T ΛS ΛT Pv α hα hP a ha _
      (mulVec_mem_of_mem_St ΛS βS _ hS hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_of_mem_St ΛT βT _ hT hh _ (pure_mem_hatL ΛT 1 (one_mem _) t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh Pv u
  refine ⟨actO_mem S T ΛS ΛT βS βT hS hT g h hg hh Pv u, fun hu => ?_⟩
  have h1 := actO_mem S T ΛS ΛT βS βT hS hT g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg)
    (by rw [map_inv]; exact inv_mem hh) Pv _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LatStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover : ∀ X : ProvA, CoverHaarIntegration X := by
  first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
section
noncomputable section

open Module

namespace GlobalTheory.QPosCompare

section Rat

variable {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} (j : X →ₛₗ[σ] E)

def IsRatSub (W : Submodule ℂ E) : Prop := Submodule.span ℂ (j '' {x | j x ∈ W}) = W

structure IsForm : Prop where
  basis : ∃ (n : ℕ) (b : Basis (Fin n) K X), LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range j) = ⊤
  inner : ∀ x y, ∃ a : K, inner ℂ (j x) (j y) = σ a

variable {j}

theorem isRatSub_span (S : Set X) : IsRatSub j (Submodule.span ℂ (j '' S)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨x, hx, rfl⟩; exact hx
  · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩

theorem IsRatSub.sup {W W' : Submodule ℂ E} (h : IsRatSub j W) (h' : IsRatSub j W') : IsRatSub j (W ⊔ W') := by
  rw [← h, ← h', ← Submodule.span_union, ← Set.image_union]
  exact isRatSub_span _

theorem IsForm.linInd (h : IsForm j) {ι : Type} [Fintype ι] {v : ι → X} (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => j (v i) := by
  obtain ⟨n, b, hb, -⟩ := h.basis
  let _ := σ.toAlgebra
  have h1 : LinearIndependent K fun i => b.equivFun (v i) :=
    hv.map' (b.equivFun : X →ₗ[K] (Fin n → K)) b.equivFun.ker
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun i => j (b i))
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hb c
      (by simpa [Fintype.linearCombination_apply] using hc)))
  suffices he : (fun i => j (v i)) = (Fintype.linearCombination ℂ fun i => j (b i)) ∘
      fun i => (algebraMap K ℂ) ∘ b.equivFun (v i) by rw [he]; exact h3
  funext i
  simp only [Function.comp, Fintype.linearCombination_apply]
  conv_lhs => rw [← b.sum_equivFun (v i)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]; rfl

theorem IsForm.finite (h : IsForm j) : FiniteDimensional K X := by
  obtain ⟨n, b, -, -⟩ := h.basis
  exact Module.Finite.of_basis b

theorem span_image_eq {T : Submodule K X} {ι : Type} [Fintype ι] (b : Basis ι K T) :
    Submodule.span ℂ (j '' (T : Set X)) = Submodule.span ℂ (Set.range fun i => j (b i)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨x, hx, rfl⟩
    have : x = ∑ i, b.equivFun ⟨x, hx⟩ i • (b i : X) := by
      have := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩; exact ⟨b i, (b i).2, rfl⟩

theorem IsForm.finrank_span (h : IsForm j) (T : Submodule K X) :
    finrank ℂ (Submodule.span ℂ (j '' (T : Set X))) = finrank K T := by
  have := h.finite
  rw [span_image_eq (finBasis K T)]
  have := finrank_span_eq_card (h.linInd ((finBasis K T).linearIndependent.map' T.subtype T.ker_subtype))
  rw [Fintype.card_fin] at this
  exact this

theorem IsForm.finrank_eq (h : IsForm j) : finrank ℂ E = finrank K X := by
  have h1 := h.finrank_span ⊤
  obtain ⟨n, b, -, hs⟩ := h.basis
  rw [Submodule.top_coe, Set.image_univ, hs] at h1
  simpa using h1

theorem IsForm.orthogonal [FiniteDimensional ℂ E] (h : IsForm j) {W : Submodule ℂ E} (hW : IsRatSub j W) :
    IsRatSub j Wᗮ := by
  have := h.finite
  choose p hp using h.inner
  set S : Submodule K X := W.comap j
  have hWS : Submodule.span ℂ (j '' (S : Set X)) = W := hW
  let b := finBasis K S
  let φ : X →ₗ[K] (Fin (finrank K S) → K) :=
    { toFun := fun x i => p (b i) x
      map_add' := fun x y => by
        funext i
        apply σ.injective
        simp only [Pi.add_apply, map_add, ← hp, inner_add_right]
      map_smul' := fun a x => by
        funext i
        apply σ.injective
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, ← hp, map_smulₛₗ, inner_smul_right] }
  have hker : LinearMap.ker φ ≤ Wᗮ.comap j := by
    intro x hx
    show j x ∈ Wᗮ
    rw [← hWS, span_image_eq b, Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      have : p (b i) x = 0 := congrFun (LinearMap.mem_ker.1 hx) i
      rw [hp, this, map_zero]
    | zero => simp
    | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
    | smul a u _ hu => rw [inner_smul_left, hu, mul_zero]
  refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩; exact hx
  · have e1 := h.finrank_span (Wᗮ.comap j)
    have e2 := Submodule.finrank_mono hker
    have e3 := φ.finrank_range_add_finrank_ker
    have e4 : finrank K (LinearMap.range φ) ≤ finrank K S := by
      simpa using (LinearMap.range φ).finrank_le
    have e5 := h.finrank_span S
    rw [hWS] at e5
    have e6 := W.finrank_add_finrank_orthogonal
    have e7 := h.finrank_eq
    have e8 : finrank ℂ (Submodule.span ℂ (j '' {x | j x ∈ Wᗮ})) = finrank K (Wᗮ.comap j) := e1
    omega

theorem IsForm.inf [FiniteDimensional ℂ E] (h : IsForm j) {W W' : Submodule ℂ E} (hW : IsRatSub j W)
    (hW' : IsRatSub j W') : IsRatSub j (W ⊓ W') := by
  have := h.orthogonal ((h.orthogonal hW).sup (h.orthogonal hW'))
  rwa [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at this

end Rat

section Twist

open Formalism.IndefR.Links

variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (s : Bool)

theorem tw_map_sub (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem tw_span (S : Set E) : Submodule.span ℂ (Tw.mk s '' S) = Tw.sub s (Submodule.span ℂ S) := by
  rw [← tw_map_sub, Submodule.map_span]; rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ}
  (h : ∀ a, σ' a = cj s (σ a)) (j : X →ₛₗ[σ] E) (f : E →ₗ[ℂ] E')

end Twist

theorem isForm_of_pres {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* G} {S : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Formalism.IndefR.Bridge.ClassPres ι S σ ρ J χ) (M : Formalism.IndefR.Links.HMod (G → W))
    (hM : M.Is (Formalism.IndefR.Bridge.AdForms ι ρ J χ) (Formalism.IndefR.Bridge.adInner ι J P.y))
    (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) : IsForm j := by
  obtain ⟨hinj, hr, hip⟩ := hM
  obtain ⟨-, ⟨hli, hsp⟩, hiso⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨⟨_, S.basis, ?_, ?_⟩, fun x y => ⟨S.csum x y, ?_⟩⟩
  · refine LinearIndependent.of_comp M.e ?_
    have : (M.e ∘ fun i => j (S.basis i)) = fun i => P.extL (S.basis i) := funext fun i => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, Submodule.map_top, hr, ← Set.range_comp]
    have : (M.e ∘ j) = P.extL := funext hj
    rw [this]; exact hsp
  · rw [hip, hj, hj]; exact hiso x y

def RatZAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {A : Formalism.L2.Indef.DefAmb Bs}
    (X : Formalism.IndefR.Cx.CxData A) (t : Bs.Tup) : Prop :=
  Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t))

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem lPos_iff_ne_bot : R.LPos F ↔ ∀ b, (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ :=
  forall_congr' fun b => pos_iff_ne_bot R F b

def ZC : Submodule ℂ (R.HX A.μ0).H := LinearMap.range (LinearMap.adjoint (R.Th A.μ0))

def RationalAtBaseWeight : Prop := RatZAt (R.toCx F) A.μ0

variable {R} in

theorem isForm_jX (h : R.IsModels) (t : T) : IsForm (R.jX t) :=
  isForm_of_pres (R.B.R t).pres (R.HX t) (h.HX t) (R.jX t) (h.jX t)

end Compare

end GlobalTheory.QPosCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealFockAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.Proof.RealFockActionTwistedOperators

open GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

theorem thetaKO_rat_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have hp : ((γ * h, g) : GA D S × GA D T) = (γ, 1) * (h, g) := by simp
  rw [hp, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)

theorem thetaKO_mul_right {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (f : WO S T → ℂ) (h u : GA D S) (g : GA D T) :
    thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have hp : ((h * u, g) : GA D S × GA D T) = (h, g) * (u, 1) := by simp
  rw [hp, map_mul, Module.End.mul_apply]

theorem adForms_rat {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    (γ : Γ) (h : G) : f (ι γ * h) = ρ γ (f h) := by
  have h1 : f (ι γ * h * ((1 : J) : G)) = (χ 1 : ℂ) • ρ γ (f h) := hf γ h 1
  simpa using h1

theorem form_rat {D : D7} {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) {γ : GA D V} (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext f (γ * h) = c.ρ (γ * h)⁻¹ (c.ρ γ (f ((finHom V).rangeRestrict h))) := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = _
  congr 1
  have hr : (finHom V).rangeRestrict (γ * h) = Bridge.ratF V ⟨γ, hγ⟩ * (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [Bridge.ratF]
  rw [hr, adForms_rat (Bridge.ratF V) hf ⟨γ, hγ⟩]
  rfl

theorem ext_mul_real {D : D7} {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) {u : GA D V} (hu : u ∈ GinfC V)
    (h : GA D V) : c.ext f (h * u) = c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict h)) := by
  have hu' : finHom V u = 1 := hu
  have hr : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [hu']
  show c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict (h * u))) = _
  rw [hr]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

end GlobalTheory.Proof.RealFockActionTwistedOperators

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGL
section
open NumberField

noncomputable section
namespace GlobalTheory.RatCount
open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal

theorem nnnorm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) d = A i j
    simp [EuclideanSpace.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem htE_entry_le_heightGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N) :
    GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤
      GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  classical
  set x : E := (γ : Matrix (Fin N) (Fin N) E) i j with hx
  set g := Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ with hg
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro v
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    have he : ((bc (compFin F E v) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j = (1 : Fv F v) ⊗ₜ[F] x := by
      change compFin F E v ((1 : AF F) ⊗ₜ[F] x) = _
      simp [compFin, Algebra.TensorProduct.map_tmul]
    rw [← he]
    exact absFin_le_normFin F v _ i j
  have hinf : ∀ w : InfinitePlace F,
      max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) ≤ htInf F w (bc (compInf F E w) g) := by
    intro w
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    refine Finset.sup_le fun τ _ => ?_
    have he : (((bc (compInf F E w) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _).map (infEmb τ)) i j = τ.1 x := by
      change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
      simp [compInf, Algebra.TensorProduct.map_tmul, infEmb_tmul]
    rw [← he]
    exact (nnnorm_entry_le_opNorm _ i j).trans ((normInf_le_iff F w).1 le_rfl τ)
  unfold htE heightGL
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => hinf w) ?_
  have hg' := finite_mulSupport_htFin F g
  refine finprod_le_finprod' (hg'.subset fun v hv hv' => hv ?_) hg' hfin
  exact le_antisymm ((hfin v).trans (le_of_eq hv')) (le_max_left _ _)

end GlobalTheory.RatCount
end
end

