import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

def colPull {k N : ℕ} (τ : Fin k → Fin N) : (Fin N → ℕ) →+ (Fin k → ℕ) where
  toFun g := g ∘ τ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colPull_single_mem {k N : ℕ} {τ : Fin k → Fin N} (hτ : Function.Injective τ) (s : Fin k) :
    colPull τ (Pi.single (τ s) 1) = Pi.single s 1 := by
  funext t
  change (Pi.single (τ s) 1 : Fin N → ℕ) (τ t) = _
  by_cases h : t = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (hτ h')), Pi.single_eq_of_ne h]

theorem colPull_single_not {k N : ℕ} {τ : Fin k → Fin N} {y : Fin N} (hy : y ∉ Set.range τ) :
    colPull τ (Pi.single y 1) = 0 := by
  funext t
  change (Pi.single y 1 : Fin N → ℕ) (τ t) = 0
  exact Pi.single_eq_of_ne (fun h => hy ⟨t, h⟩) _

theorem mem_dualWeyl_iff' {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem aeval_isWeightedHomogeneous {R σ ι Mo : Type} [CommRing R] [AddCommMonoid Mo] (w : ι → Mo)
    (φ : σ → MvPolynomial ι R) (ω : σ → Mo) (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v))
    (x : MvPolynomial σ R) (κ : Mo) (hx : IsWeightedHomogeneous ω x κ) :
    IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem isWeightedHomogeneous_map_weight {R σ M M' : Type} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
    (π : M →+ M') (w : σ → M) (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

theorem substMem : SubstMem := by
  intro R _ k N τ hτ ψ h1 h2 h3 ν f hf
  rw [mem_dualWeyl_iff'] at hf ⊢
  have hinj := hτ.injective
  refine ⟨?_, fun l j hlj => ?_⟩
  · have hvar : ∀ v : Fin N × Fin N,
        IsWeightedHomogeneous (colW k k) (ψ v) (colPull τ (colW N N v)) := by
      rintro ⟨x, y⟩
      change IsWeightedHomogeneous _ _ (colPull τ (Pi.single y 1))
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        rw [colPull_single_mem hinj]
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1]
          exact isWeightedHomogeneous_X _ _ _
        · rw [h2 x s hx]
          exact isWeightedHomogeneous_zero _ _ _
      · rw [colPull_single_not hy]
        obtain ⟨c, hc⟩ := h3 x y hy
        rw [hc]
        exact isWeightedHomogeneous_C _ _
    exact aeval_isWeightedHomogeneous (colW k k) ψ _ hvar f _
      (isWeightedHomogeneous_map_weight (colPull τ) _ f ν hf.1)
  · let ψO : Option (Fin N × Fin N) → MvPolynomial (Option (Fin k × Fin k)) R :=
      fun o => o.elim (X none) fun v => rename some (ψ v)
    have hA : (aeval ψO).comp (rename some) = (rename some).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      simp [ψO]
    have hB : (aeval ψO).comp (colAddGen R (r := N) (τ l) (τ j)) = (colAddGen R l j).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨x, y⟩ := v
      simp only [AlgHom.comp_apply, aeval_X]
      rw [colAddGen, aeval_X]
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1, colAddGen, aeval_X]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h1]
          · simp [ψO, h1]
        · rw [h2 x s hx, map_zero]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h2 x _ hx]
          · simp [ψO, h2 x _ hx]
      · obtain ⟨c, hc⟩ := h3 x y hy
        have hyj : y ≠ τ j := fun h => hy ⟨j, h.symm⟩
        rw [if_neg hyj, hc]
        simp [ψO, hc]
    have e1 := congrArg (fun φ => φ f) hA
    have e2 := congrArg (fun φ => φ f) hB
    simp only [AlgHom.comp_apply] at e1 e2
    rw [← e2, hf.2 (τ l) (τ j) (hτ hlj), e1]

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section
namespace GlobalTheory.LeviCut

theorem mem_range_map_of_flat {M1 M2 : Type} [AddCommGroup M1] [AddCommGroup M2]
    (N1 : Submodule ℤ M1) (N2 : Submodule ℤ M2) [Module.Flat ℤ (M2 ⧸ N2)] (z : M1 ⊗[ℤ] M2)
    (h1 : z ∈ LinearMap.range (LinearMap.lTensor M1 N2.subtype))
    (h2 : z ∈ LinearMap.range (LinearMap.rTensor M2 N1.subtype)) :
    z ∈ LinearMap.range (TensorProduct.map N1.subtype N2.subtype) := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨w, rfl⟩ := h2
  have hw : LinearMap.lTensor N1 N2.mkQ w = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M2 ⧸ N2) N1.subtype N1.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, ← hu, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : N2.mkQ ∘ₗ N2.subtype = 0 := by ext x; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w', hw'⟩ := (lTensor_exact N1 (LinearMap.exact_subtype_mkQ N2) N2.mkQ_surjective w).1 hw
  refine ⟨w', ?_⟩
  rw [← hw', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]

theorem flat_quot_dualWeyl (q : ℕ) (ν : Fin q → ℕ) :
    Module.Flat ℤ (MvPolynomial (Fin q × Fin q) ℤ ⧸ dualWeyl ℤ q q ν) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨⟨c, hc⟩, hcx⟩ := (Submodule.mem_torsion_iff x).1 hx
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have : c • f ∈ dualWeyl ℤ q q ν := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; simpa using hcx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact dualWeylSat ℤ q q ν c f hc0 this

theorem bidet_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

def psiR (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun s => C (X (a, s))) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun _ => 0) (fun t => X (b, t)) v.2) v.1

def psiL (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun s => X (a, s)) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun _ => 0) (fun t => C (X (b, t))) v.2) v.1

def phiR (p q : ℕ) : MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom Algebra.TensorProduct.includeLeftRingHom (fun v => 1 ⊗ₜ X v)

def phiL (p q : ℕ) : MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom (Algebra.TensorProduct.includeRight : MvPolynomial (Fin q × Fin q) ℤ →ₐ[ℤ] _).toRingHom
    (fun v => X v ⊗ₜ 1)

theorem phiR_psiR (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiR p q (aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f)) = resT ℤ p q f := by
  have : (phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiR, psiR, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiL_psiL (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiL p q (aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f)) = resT ℤ p q f := by
  have : (phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiL, psiL, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiR_map (p q : ℕ) (h : MvPolynomial (Fin q × Fin q) ℤ) :
    phiR p q (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) h) = 1 ⊗ₜ h := by
  have : (phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)) =
      (Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))).comp C) (((Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom).comp C)) r
    intro v; (simp [phiR])
  exact DFunLike.congr_fun this h

theorem phiL_map (p q : ℕ) (h : MvPolynomial (Fin p × Fin p) ℤ) :
    phiL p q (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) h) = h ⊗ₜ 1 := by
  have : (phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)) =
      (Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))).comp C) (((Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom).comp C)) r
    intro v; (simp [phiL])
  exact DFunLike.congr_fun this h

theorem mul_mem_range_lTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ B) (u : A)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.lTensor A N.subtype)) :
    (u ⊗ₜ (1 : B)) * x ∈ LinearMap.range (LinearMap.lTensor A N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => exact ⟨(u * a) ⊗ₜ n, by simp⟩
  | add x y hx hy => rw [map_add, mul_add]; exact add_mem hx hy

theorem mul_mem_range_rTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ A) (u : B)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.rTensor B N.subtype)) :
    ((1 : A) ⊗ₜ u) * x ∈ LinearMap.range (LinearMap.rTensor B N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n b => exact ⟨n ⊗ₜ (u * b), by simp⟩
  | add x y hx hy => rw [map_add, mul_add]; exact add_mem hx hy

theorem resT_mem_lTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ)
      (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype) := by
  have hg : aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin p × Fin p) ℤ) q q (fun j => ν (Fin.natAdd p j)) := by
    refine hS (MvPolynomial (Fin p × Fin p) ℤ) q (p + q) (Fin.natAdd p) (Fin.strictMono_natAdd p) (psiR p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiR]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => simp [psiR]
      | right b => exact absurd ⟨b, rfl⟩ hx
    · intro x y hy
      induction y using Fin.addCases with
      | right t => exact absurd ⟨t, rfl⟩ hy
      | left s =>
        induction x using Fin.addCases with
        | left a => exact ⟨X (a, s), by simp [psiR]⟩
        | right b => exact ⟨0, by simp [psiR]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiR_psiR]
  refine Submodule.span_induction (p := fun g _ => phiR p q g ∈ LinearMap.range
    (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ) (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ), phiR_map]
    exact ⟨1 ⊗ₜ ⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ q q K sz hsz I⟩, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiR p q (C u) = u ⊗ₜ 1 := by simp [phiR]
    rw [this]; exact mul_mem_range_lTensor _ u _ hx

theorem resT_mem_rTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ)
      (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype) := by
  have hg : aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin q × Fin q) ℤ) p p (fun i => ν (Fin.castAdd q i)) := by
    refine hS (MvPolynomial (Fin q × Fin q) ℤ) p (p + q) (Fin.castAdd q) (Fin.strictMono_castAdd q) (psiL p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiL]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => exact absurd ⟨a, rfl⟩ hx
      | right b => simp [psiL]
    · intro x y hy
      induction y using Fin.addCases with
      | left s => exact absurd ⟨s, rfl⟩ hy
      | right t =>
        induction x using Fin.addCases with
        | left a => exact ⟨0, by simp [psiL]⟩
        | right b => exact ⟨X (b, t), by simp [psiL]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiL_psiL]
  refine Submodule.span_induction (p := fun g _ => phiL p q g ∈ LinearMap.range
    (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ) (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ), phiL_map]
    exact ⟨⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ p p K sz hsz I⟩ ⊗ₜ 1, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiL p q (C u) = 1 ⊗ₜ u := by simp [phiL]
    rw [this]; exact mul_mem_range_rTensor _ u _ hx

def toQ (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ →+*
    MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ :=
  (Algebra.TensorProduct.lift
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeLeftRingHom).comp (map (Int.castRingHom ℚ))))
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeRight :
      MvPolynomial (Fin q × Fin q) ℚ →ₐ[ℚ] MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] _).toRingHom.comp
        (map (Int.castRingHom ℚ))))
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQ_tmul (p q : ℕ) (a : MvPolynomial (Fin p × Fin p) ℤ) (b : MvPolynomial (Fin q × Fin q) ℤ) :
    toQ p q (a ⊗ₜ b) = intQ p p a ⊗ₜ intQ q q b := by
  simp [toQ, intQ, RingHom.toIntAlgHom_apply]

theorem toQ_resT (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    toQ p q (resT ℤ p q f) = resT ℚ p q (intQ (p + q) (p + q) f) := by
  have : (toQ p q).comp (resT ℤ p q).toRingHom = (resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((toQ p q).comp (resT ℤ p q).toRingHom).comp C)
        (((resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ))).comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [toQ, resT, resVarT, RingHom.toIntAlgHom_apply]
  exact RingHom.congr_fun this f

theorem resLat_of_substMem : SubstMem → ResLat := by
  intro hS p q ν f hf
  have := flat_quot_dualWeyl q (fun j => ν (Fin.natAdd p j))
  obtain ⟨w, hw⟩ := mem_range_map_of_flat (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)))
    (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))) (resT ℤ p q f)
    (resT_mem_lTensor hS p q ν f hf) (resT_mem_rTensor hS p q ν f hf)
  rw [← toQ_resT, ← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, toQ_tmul]
    exact Submodule.subset_span ⟨a.1, a.2, b.1, b.2, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleGeomDescent

open scoped TensorProduct

theorem eq_of_geometric_points' {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rwa [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this

theorem descent : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ _ hff het b hb
  have hBr : _root_.IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced A B
  have : Algebra.Smooth B (B ⊗[A] B) := inferInstance
  have hCr : _root_.IsReduced (B ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B (B ⊗[A] B)
  have hC : (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b := by
    refine eq_of_geometric_points' _ _ fun k _ _ χ => ?_
    have key := hb k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom) ?_
    · simpa using key
    · ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hx := (Algebra.IsEffective.of_faithfullyFlat A B b).mp (by simp [hC])
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha⟩

end GlobalTheory.EtaleGeomDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartPreirreducibleFiber
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_open_inter_fiber_subset_sectionComponent (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (s : S) :
    ∃ W₁ : X.Opens, e s ∈ W₁ ∧ ∀ x : X, x ∈ W₁ → f x = s →
      x ∈ connectedComponentIn (f ⁻¹' {s}) (e s) := by
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hrange : Set.range (f.fiberι s) = f ⁻¹' {s} := f.range_fiberι s
  obtain ⟨y₀, hy₀⟩ : e s ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hes
  have hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback hpb inferInstance
  have hN : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have hopen := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hN y₀
  obtain ⟨U, hU, hUe⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · change e s ∈ U
    rw [← hy₀]
    have : y₀ ∈ connectedComponent y₀ := mem_connectedComponent
    rw [← hUe] at this
    exact this
  · intro x hx hxs
    obtain ⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hxs
    refine (GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e s _ _ _ y₀ hpb hy₀ y).mpr ?_
    rw [← hUe]
    exact hx

theorem exists_affine_chart_preirreducible_fiber : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  intro X S f e hf he s
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨W₁, hW₁, hW₁'⟩ := exists_open_inter_fiber_subset_sectionComponent X S f e hf he s
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hmem : e s ∈ ((W₁ ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := ⟨hW₁, by
    change f (e s) ∈ (V : Set S)
    rw [hes]; exact hsV⟩
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hsW, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hmem (W₁ ⊓ f ⁻¹ᵁ V).isOpen
  refine ⟨V, W, fun x hx => (hle hx).2, hV, hW, hsW, ?_⟩
  intro k _ p hp
  let e' : Spec (CommRingCat.of k) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'' : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  have h1 := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S _ _ f (pullback.snd f p) p (pullback.fst f p) e e' hf
    (IsPullback.of_hasPullback f p) he he' he''
  have h2 := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k _ (pullback.snd f p) e' inferInstance he').2
  rw [← h1] at h2
  let j : pullback (W.ι ≫ f) p ⟶ pullback f p :=
    pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hj : IsOpenImmersion j := inferInstance
  have hjf : j ≫ pullback.fst f p = pullback.fst _ _ ≫ W.ι := pullback.lift_fst _ _ _
  have h3 := h2.isPreirreducible.preimage j.isOpenEmbedding
  constructor
  convert h3 using 1
  symm
  rw [Set.eq_univ_iff_forall]
  intro y
  have hx : f (pullback.fst f p (j y)) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hp]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  change pullback.fst f p (j y) ∈ connectedComponentIn (f ⁻¹' {f (pullback.fst f p (j y))})
    (e (f (pullback.fst f p (j y))))
  rw [hx]
  refine hW₁' _ ?_ hx
  rw [← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply]
  exact (hle (pullback.fst (W.ι ≫ f) p y).2).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBotStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
end

