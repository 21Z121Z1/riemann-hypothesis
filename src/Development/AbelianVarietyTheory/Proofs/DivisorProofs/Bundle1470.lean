import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblESymmToLinearMap
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem elim_dot' {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

section Coord

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) w w' = hTens c JA JB w.toCols₁ w'.toCols₁ - hTens c JA JB w.toCols₂ w'.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.toCols₁_apply, Matrix.toCols₂_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) w w' = symp c ξ JA JB w.toCols₁ w'.toCols₁ - symp c ξ JA JB w.toCols₂ w'.toCols₂ := by
  unfold symp
  rw [hTens_dbl, mul_sub, map_sub]

variable [Invertible (2 : R)] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

def dblCo (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun w => (Sum.elim (d.e w.toCols₁).1 (d.e w.toCols₂).1, Sum.elim (d.e w.toCols₁).2 (-(d.e w.toCols₂).2))
      map_add' := fun w w' => by
        have h1 : (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ := by ext; simp
        have h2 : (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ := by ext; simp
        rw [h1, h2, map_add, map_add]
        ext k <;> cases k <;> simp [add_comm]
      map_smul' := fun a w => by
        have h1 : (a • w).toCols₁ = a • w.toCols₁ := by ext; simp
        have h2 : (a • w).toCols₂ = a • w.toCols₂ := by ext; simp
        rw [h1, h2, map_smul, map_smul]
        ext k <;> cases k <;> simp
      invFun := fun p => Matrix.fromCols (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      left_inv := fun w => by
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_neg, Prod.mk.eta, LinearEquiv.symm_apply_apply]
        exact Matrix.fromCols_toCols w
      right_inv := fun p => by
        simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply, neg_neg,
          Sum.elim_comp_inl_inr] }
  form w w' := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [symp_dbl, d.form, d.form, elim_dot', elim_dot', dotProduct_neg, dotProduct_neg]
    ring

theorem dblCo_isDblCoord (d : Darboux (symp c ξ JA JB) κ) : IsDblCoord c ξ JA JB d (dblCo c d) := fun w₁ w₂ => by
  simp [dblCo]

end Coord

section Equivs

variable {R : Type}

def conjE {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

theorem conjE_apply {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) (φ : X → ℂ) : conjE T φ = star (T (star φ)) := rfl

def partLE {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partRE {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblE {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partRE (conjE T)).trans (partLE T)

end Equivs

end GlobalTheory.DblInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
section
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThK.RealLineGrowthDerivative
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem hr_smul_eq (R : Type) [CommRing R] [Algebra F R] (M : Matrix (Fin n) (Fin n) E) {c₀ c₁ : E} (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    HR R σ (c₀ • M) = HR R σ (c₁ • M) := by
  have key : ∀ c : E, c ≠ 0 → ∀ g : GL (Fin n) (R ⊗[F] E), g ∈ HR R σ (c • M) ↔ g ∈ HR R σ M := by
    intro c hc g
    have hu : IsUnit (inclR (F := F) R c) := (IsUnit.mk0 c hc).map _
    have e : JR (F := F) R (c • M) = inclR (F := F) R c • JR (F := F) R M :=
      Matrix.ext fun i j => map_mul (inclR (F := F) R) c (M i j)
    change Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _ ↔ Formalism.UG.cT _ g.1 * JR (F := F) R _ * g.1 = JR (F := F) R _
    rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]
  ext g
  rw [key c₀ h₀, key c₁ h₁]

theorem isRealLine_move (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) {c₀ c₁ : E} (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)
    {γ : ℝ → GAd σ (c₀ • J.map σ)} (hγ : IsRealLine σ (c₀ • J.map σ) γ) :
    IsRealLine σ (c₁ • J.map σ) (fun t => toGAd hσ J h₁ ((toGAd hσ J h₀).symm (γ t))) := by
  obtain ⟨w, τ, Z, hZ, hy⟩ := hγ
  have hmap : ∀ c : E, (c • J.map σ).map τ.1 = τ.1 c • (J.map σ).map τ.1 := fun c =>
    Matrix.ext fun i j => map_mul τ.1 c _
  have hZ' : Zᴴ * (J.map σ).map τ.1 + (J.map σ).map τ.1 * Z = 0 := by
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hZ
    exact (smul_eq_zero.1 hZ).resolve_left ((map_ne_zero τ.1).2 h₀)
  refine ⟨w, τ, Z, by rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hZ', smul_zero], fun t => ?_⟩
  obtain ⟨y, e1, e2⟩ := hy t
  refine ⟨⟨y.1, (SetLike.ext_iff.1 (hr_smul_eq _ (J.map σ) h₀ h₁) y.1).1 y.2⟩, ?_, e2⟩
  apply Subtype.ext
  show ((toGAd hσ J h₀).symm (γ t)).1 = _
  rw [e1]
  rfl

theorem foldr_lineDer_comp {K₀ K₁ : Matrix (Fin n) (Fin n) E} (e : GAd σ K₀ ≃* GAd σ K₁) (f : GAd σ K₁ → ℂ) :
    ∀ l : List (ℝ → GAd σ K₀), l.foldr lineDer (fun x => f (e x)) =
      fun x => (l.map fun γ t => e (γ t)).foldr lineDer f (e x) := by
  intro l
  induction l with
  | nil => rfl
  | cons γ l ih =>
    funext x
    simp only [List.foldr_cons, List.map_cons, ih, lineDer, map_mul]

variable {J : Matrix (Fin n) (Fin n) E}

theorem prod_ofFn_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_partial_last {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun s : Fin m → ℝ => deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 := by
  let v : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  let L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i
  have hL : ∀ s t, Fin.snoc (α := fun _ => ℝ) s t = L s + t • v := fun s t => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, v]
    · simp [L, v, Fin.castSucc_ne_last]
  have hd : ∀ s, deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by
    simp only [hL]
    have h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)
    have h2 := (hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)
    rw [zero_smul, add_zero] at h2
    have h3 := h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h3.deriv
  simp only [hd]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const

theorem contDiff_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ (m : ℕ) (δ : Fin m → ℝ → GAd σ J),
      (∀ i, IsRealLine σ J (δ i)) → ∀ x,
      ContDiff ℝ ∞ fun s : Fin m → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => δ i (s i)).prod) := by
  intro l
  induction l with
  | nil => intro _ m δ hδ x; exact hf m δ hδ x
  | cons γ l ih =>
    intro hl m δ hδ x
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    have hH := ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ)
      (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x
    have := contDiff_partial_last hH
    simp only [prod_ofFn_snoc, ← mul_assoc] at this
    simpa only [List.foldr_cons, lineDer] using this

theorem differentiableAt_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (x : GAd σ J) :
    DifferentiableAt ℝ (fun t => l.foldr lineDer f (x * γ t)) 0 := by
  have h := (contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

theorem foldr_lineDer_sub {f₁ f₂ : GAd σ J → ℂ} (hf₁ : GlobalTheory.UAut.IsSm σ J f₁) (hf₂ : GlobalTheory.UAut.IsSm σ J f₂) (c : ℂ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (fun x => f₁ x - c * f₂ x) = fun x => l.foldr lineDer f₁ x - c * l.foldr lineDer f₂ x := by
  intro l hl
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    funext x
    simp only [List.foldr_cons, ih hl', lineDer]
    have d1 := differentiableAt_foldr_lineDer hf₁ l hl' hγ x
    have d2 := differentiableAt_foldr_lineDer hf₂ l hl' hγ x
    exact (d1.hasDerivAt.sub (d2.hasDerivAt.const_mul c)).deriv

end GlobalTheory.ThK.RealLineGrowthDerivative

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroup
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

namespace GlobalTheory.RatUDiscreteSub

theorem discreteTopology_subgroupOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)),
    DiscreteTopology ((ratU σ J).subgroupOf N) := by
  intro F E _ _ _ _ _ σ n J N
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  let φ : (ratU σ J).subgroupOf N → ratU σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have h2 : Topology.IsEmbedding (fun x : (ratU σ J).subgroupOf N => ((x : N) : UA σ J)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hφ : Topology.IsEmbedding φ :=
    (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal (p := fun x : UA σ J => x ∈ ratU σ J))).1 h2
  exact hφ.discreteTopology

end GlobalTheory.RatUDiscreteSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0Statement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank : ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V), Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) → (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  first | exact @GlobalTheory.dixmier_schur_of_rank_le_aleph0 | exact GlobalTheory.dixmier_schur_of_rank_le_aleph0 | (intros; apply GlobalTheory.dixmier_schur_of_rank_le_aleph0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConjStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFockVacuum_eq_smul_vacuum_mul_conj : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  first | exact @GlobalTheory.RealLift.VacBox.vac_box | exact GlobalTheory.RealLift.VacBox.vac_box | (intros; apply GlobalTheory.RealLift.VacBox.vac_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCellStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v, GlobalTheory.DblVac.BigCell W v g →
      ∃ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W ∧ ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ g = q * p := by
  first | exact @GlobalTheory.DblVacGauss.gauss_decomp | exact GlobalTheory.DblVacGauss.gauss_decomp | (intros; apply GlobalTheory.DblVacGauss.gauss_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {j : K →+* K'}

theorem exists_genFib_baseChange (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K')))
    (m : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) :
    ∃ (Q : Out.PolAV (Sp K')) (hd : SmoothOfRelativeDimension F.P₀.g Q.A.hom) (φ' : Q.A.left ⟶ T'.t.G.left)
      (fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim Q F.P₀.g hd) φ')
      (v' : Fin F.P₀.g → (epsR K' ⟶ Q.A)) (basis : IsLieBasis v'),
      (∀ τ : 𝓞 E →+* 𝓞 K, (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).eigLat T'.t.act
          ((RingOfIntegers.mapRingHom j).comp τ) =
        Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)))) ∧
      ∀ (u : epsR (𝓞 K) ⟶ T.t.G) (c : Fin F.P₀.g → K), F.IsCoord u c → ∀ u' : epsR (𝓞 K') ⟶ T'.t.G,
        IsVecOver (RingOfIntegers.mapRingHom j) m.φ u u' →
        (GenFib.mk (withDim Q F.P₀.g hd) φ' fib v' basis : GenFib T'.pol).IsCoord u' (fun i => j (c i)) := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hB : Out.PolBaseChangeSt := hL.polBaseChange
  have hdT : SmoothOfRelativeDimension T.g T'.t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m.cart.1 T.dim
  have hξ : IsPolFibre (RingOfIntegers.mapRingHom j) T.pol T'.pol m.φ :=
    ⟨H1.dim_unique _ T'.dim hdT (eSec T'.t.G (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 K'))), m.cart,
      (PAT.exists_of_sabMap E H _ _ _ T T'.t m).2⟩
  obtain ⟨F'⟩ := GenFib.nonempty_of_baseChange hB K' T'.pol
  have hg : F'.P₀.g = F.P₀.g := F'.fib.1.trans (hξ.1.trans F.fib.1.symm)
  have hd : SmoothOfRelativeDimension F.P₀.g F'.P₀.A.hom := hg ▸ F'.P₀.smoothDim
  have fib : IsPolFibre (algebraMap (𝓞 K') K') T'.pol (withDim F'.P₀ F.P₀.g hd) F'.φ := ⟨hg.symm.trans F'.fib.1, F'.fib.2⟩
  obtain ⟨ψ, hψ, w⟩ := PolFibre.cancel (g := j) F.fib (PolFibre.comp hξ fib)
  haveI := F.P₀.isAb.comm
  haveI := F'.P₀.isAb.comm
  haveI := F.P₀.smoothDim
  obtain ⟨v', basis, hv⟩ := exists_isLieBasis_baseChange K K' j F.P₀.A F'.P₀.A ψ hψ.2.1
    (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
  refine ⟨F'.P₀, hd, F'.φ, fib, v', basis, fun τ => ?_, fun u c hc u' hu => ?_⟩
  · exact eigLat_eq_span hB hξ hψ.2.1 w hv T.t.act T'.t.act m.act τ
  · exact isCoord_over hξ.2.1 hψ.2.1 w hv hc hu

end GlobalTheory.CM.LieSpanBaseChange
end

noncomputable section
namespace GlobalTheory.CM.LieSpanBaseChange

open GlobalTheory.CM.LieBaseChange GlobalTheory.CM.IntCoord

theorem eigLat_image_le_span_diff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB n f f' g' _ hf' hg' hff' hid FA FB M hM τ w hw
  obtain ⟨QA, hdA, φA, fibA, vA, bA, hA1, hA2⟩ := exists_genFib_baseChange A A' mA FA
  obtain ⟨QB, hdB, φB, fibB, vB, bB, hB1, hB2⟩ := exists_genFib_baseChange B B' mB FB
  let F₁A : GenFib A'.pol := GenFib.mk (withDim QA FA.P₀.g hdA) φA fibA vA bA
  let F₁B : GenFib B'.pol := GenFib.mk (withDim QB FB.P₀.g hdB) φB fibB vB bB
  have hcB := GlobalTheory.T.integral_tangent_vector_coordinates K' _ F₁B
  choose M' hM' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' A'.pol F₁A B'.pol F₁B (f' i) (hf' i).isMonHom).1).exists
  choose N' hN' using fun i =>
    ((DiffCoord.existsUnique_isDiffOf K' B'.pol F₁B A'.pol F₁A (g' i) (hg' i).isMonHom).1).exists
  set S := Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) with hSdef
  have hjadd : ∀ {m : ℕ} (x y : Fin m → K), (fun k => j ((x + y) k)) = (fun k => j (x k)) + (fun k => j (y k)) :=
    fun x y => funext fun k => by simp
  have hjsmul : ∀ {m : ℕ} (r : 𝓞 K) (x : Fin m → K),
      (fun k => j ((r • x) k)) = (RingOfIntegers.mapRingHom j r) • (fun k => j (x k)) :=
    fun r x => funext fun k => by
      rw [← algebraMap_smul K r x, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, ← algebraMap_smul K',
        smul_eq_mul]
      rfl
  have hcomp : ∀ i, ∀ e ∈ FA.eigLat A.t.act τ, M' i (fun k => j (e k)) = fun k => j (M i e k) := by
    intro i e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, -⟩ := hx
      obtain ⟨u', hu', -⟩ := existsUnique_isVecOver mA.cart.1 u
      have h1 := hM' i u' _ (hA2 u x hu u' hu')
      have h2 := hB2 (u ≫ f i) (M i x) (hM i u x hu) (u' ≫ f' i) (by
        unfold IsVecOver at hu' ⊢
        rw [Over.comp_left, Over.comp_left, Category.assoc, hff' i, ← Category.assoc, hu', Category.assoc])
      exact (hcB.1 _ h1.1).unique h1 h2
    | zero =>
      have h0 : (fun k => j ((0 : Fin FA.P₀.g → K) k)) = 0 := funext fun k => by simp
      rw [h0, map_zero, map_zero]
      funext k
      simp
    | add x y _ _ hx hy =>
      rw [hjadd, map_add, hx, hy, map_add, hjadd]
    | smul r x _ hx =>
      rw [hjsmul, ← algebraMap_smul K' (RingOfIntegers.mapRingHom j r), map_smul, hx, algebraMap_smul,
        ← algebraMap_smul K r x, map_smul, algebraMap_smul, hjsmul]
  have hS : ∀ i, ∀ x ∈ Submodule.span (𝓞 K') ((fun (c : Fin FA.P₀.g → K) k => j (c k)) ''
      (FA.eigLat A.t.act τ : Set (Fin FA.P₀.g → K))), M' i x ∈ S := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [hcomp i e he]
      exact Submodule.subset_span ⟨M i e, ⟨i, e, he, rfl⟩, rfl⟩
    | zero =>
      rw [map_zero]
      exact S.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul s x _ hx =>
      rw [← algebraMap_smul K' s x, map_smul, algebraMap_smul]
      exact S.smul_mem s hx
  have hkey : F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro c' ⟨u', hu', heig⟩
    have hN'mem : ∀ i, N' i c' ∈ F₁A.eigLat A'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := fun i =>
      Indep.map_eigLat_le (hg' i).comm (hN' i) _
        (Submodule.mem_map_of_mem (f := (N' i).restrictScalars (𝓞 K')) (Submodule.subset_span ⟨u', hu', heig⟩))
    have hs : ∀ i, F₁B.IsCoord (u' ≫ (g' i ≫ f' i)) (M' i (N' i c')) := fun i => by
      rw [← Category.assoc]
      exact hM' i _ _ (hN' i _ _ hu')
    have hprod : ∀ s : Finset (Fin n),
        F₁B.IsCoord (u' ≫ ∏ i ∈ s, (g' i ≫ f' i)) (∑ i ∈ s, M' i (N' i c')) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.sum_empty, comp_one]
        exact isCoord_one F₁B
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
        exact isCoord_mul F₁B (hs a) ih
    have h1 := hprod Finset.univ
    rw [hid, Category.comp_id] at h1
    have heq : c' = ∑ i, M' i (N' i c') := (hcB.1 _ hu'.1).unique hu' h1
    rw [heq]
    refine S.sum_mem fun i _ => hS i _ ?_
    rw [← hA1 τ]
    exact hN'mem i
  have hw' : (fun k => j (w k)) ∈ F₁B.eigLat B'.t.act ((RingOfIntegers.mapRingHom j).comp τ) := by
    rw [hB1 τ]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  exact hkey hw'

end GlobalTheory.CM.LieSpanBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

theorem ell_coeff_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  intro E _ _ _ n P hP
  have hdeg : P.natDegree = n := hP.2.1
  obtain ⟨h0, hid⟩ := ell_conj_selfRecip E n P hP
  refine ⟨h0, fun k hk => ?_⟩
  have hc := congrArg (fun Q : E[X] => Q.coeff k) hid
  simp only [coeff_C_mul, coeff_reverse] at hc
  have hnd : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (IsCMField.complexConj E).toRingEquiv.toRingHom.injective, hdeg]
  rw [hnd, revAt_le hk, coeff_map] at hc
  have hc2 := congrArg (IsCMField.complexConj E) hc
  simpa [map_mul] using hc2

end GlobalTheory.ConjSelfRecip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizerStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  first | exact @GlobalTheory.CptTorus.main | exact GlobalTheory.CptTorus.main | (intros; apply GlobalTheory.CptTorus.main <;> assumption)
end

