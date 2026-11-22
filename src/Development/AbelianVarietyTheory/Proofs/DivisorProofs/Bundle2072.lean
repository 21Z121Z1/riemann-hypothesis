import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblSplitForm

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_ext_form (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) (l0 : M →ₗ[ℂ] ℂ) (gen : Set M)
    (hinv : ∀ u ∈ Y, ∀ p ∈ gen, l0 (ρ u p) = l0 p) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ∀ p ∈ gen, ℓ p = l0 p := by
  classical
  let P : Submodule ℂ M := Submodule.span ℂ gen
  let K : Submodule ℂ M := Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}
  have hl0P : ∀ u ∈ Y, ∀ p ∈ P, l0 (ρ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf => exact hinv u hu f hf
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, -⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero hadd h0 hsm hmK
    have h1 : l0 (∑ j ∈ s, ρ (y j) m) = (s.card : ℂ) * l0 m := by
      rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc
  let fP : M →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : M →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : M) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : M) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu g hg => ?_, fun p hp => ?_⟩
  · have hk : ρ u g - g ∈ K := Submodule.subset_span ⟨u, hu, g, hg, rfl⟩
    have hz : ρ u g - g ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (ρ u g - g) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp' : p ∈ P := Submodule.subset_span hp
    have hz : p ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp'
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp'⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 p + 0 = _
    rw [add_zero]

end Abstract

def conjForm {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := conj (ℓ (fun y => conj (g y)))
  map_add' a b := by
    have : (fun y => conj ((a + b) y)) = (fun y => conj (a y)) + fun y => conj (b y) := by
      funext y; simp
    rw [this, map_add, map_add]
  map_smul' c a := by
    have : (fun y => conj ((c • a) y)) = conj c • fun y => conj (a y) := by
      funext y; simp
    rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]

theorem conjForm_mul {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (b : X → ℂ) :
    conjForm ℓ (fun y => c * conj (b y)) = c * conj (ℓ b) := by
  have : (fun y => conj (c * conj (b y))) = conj c • b := by
    funext y; simp
  show conj (ℓ (fun y => conj (c * conj (b y)))) = _
  rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def joinR (x₁ x₂ : WOF F E nS nT) : WOF F E nS (nT + nT) := (Matrix.fromRows x₁ x₂).submatrix finSumFinEquiv.symm id

theorem topR_joinR (x₁ x₂ : WOF F E nS nT) : topR (joinR x₁ x₂) = x₁ := by
  ext i j
  simp [joinR, topR, Matrix.submatrix_apply]

theorem botR_joinR (x₁ x₂ : WOF F E nS nT) : botR (joinR x₁ x₂) = x₂ := by
  ext i j
  show Matrix.fromRows x₁ x₂ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j = x₂ i j
  rw [Equiv.symm_apply_apply]; rfl

def dblForm (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ :=
  ℓ ∘ₗ LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y))

theorem dblForm_deltaT (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) (a b : WOF F E nS nT → ℂ) :
    dblForm ℓ (deltaT a b) = ℓ a * conj (ℓ b) := by
  have h : (LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y)))
      (deltaT a b) = conj (ℓ b) • a := by
    funext x₁
    have e : (LinearMap.funLeft ℂ ℂ (fun y : WOF F E nS nT => joinR x₁ (-y))) (deltaT a b) =
        fun y => a x₁ * conj (b y) := by
      funext y
      simp [LinearMap.funLeft_apply, deltaT_apply, topR_joinR, botR_joinR]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, e, conjForm_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dblForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DblSplitForm

namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

theorem exists_invForm_dbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    GlobalTheory.T.exists_nonzero_thetaFun_oriented_model_cm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := GlobalTheory.T.exists_splitPlace_conjHeisenberg_invariantForm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := GlobalTheory.DblHeis.heisOF_dblG_deltaT F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)

end GlobalTheory.DblSplitForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.WhitBase

section SlopeTestRemainingChoices

open Formalism.L2.DIV

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

theorem isUniUp_map_iff (f : κ ≃+* κ') (M : GL (Fin r) κ) :
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') ↔
      M ∈ unip κ r := by
  have hc : ∀ a b, ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f ((M : Matrix (Fin r) (Fin r) κ) a b) := fun a b => rfl
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := (h i j).1 hij
      rw [hc] at this
      exact f.injective (by rw [this, map_zero])
    · have := (h i i).2 rfl
      rw [hc] at this
      exact f.injective (by rw [this, map_one])
  · intro h a b
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · rw [hc, unip_lower h hab, map_zero]
    · subst hab
      rw [hc, unip_diag h, map_one]

theorem edgeSum_supEdge_eq (M : GL (Fin r) κ) :
    edgeSum supEdge M = ∑ i ∈ Finset.range (r - 1), Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1) := by
  classical
  have h1 : ∀ i : Fin r, (∑ j : Fin r, if supEdge i j then (M : Matrix (Fin r) (Fin r) κ) i j else 0) =
      Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i.val (i.val + 1) := by
    intro i
    unfold Formalism.MainNotions.ArithmeticCylinders.entN
    by_cases hi : i.val + 1 < r
    · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
      · rw [if_pos (show supEdge i ⟨i.val + 1, hi⟩ from rfl), dif_pos ⟨i.isLt, hi⟩]
      · intro j _ hj
        rw [if_neg (show ¬ supEdge i j from fun e => hj (Fin.ext e))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg (by omega)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (show ¬ supEdge i j from fun e => by
        have := j.isLt
        unfold supEdge at e
        omega)]
  unfold edgeSum
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1)) r]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    have : Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) s (s + 1) = 0 := by
      unfold Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dif_neg (by omega)]
    rw [this, add_zero]

theorem entN_map (f : κ ≃+* κ') (M : GL (Fin r) κ) (a b : ℕ) :
    Formalism.MainNotions.ArithmeticCylinders.entN ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f (Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) a b) := by
  unfold Formalism.MainNotions.ArithmeticCylinders.entN
  split_ifs
  · rfl
  · rw [map_zero]

end SlopeTestRemainingChoices

section Comparison₂

open Formalism.L2.DIV Formalism.BasicNotions

variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}

theorem mem_iff_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : G) :
    g ∈ P0 ↔ ∀ kv, Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((eG g kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [h.p0 g]
  show eC g ∈ Subgroup.pi Set.univ _ ↔ _
  rw [Subgroup.mem_pi]
  constructor
  · intro hx kv
    rw [h.comp g kv, isUniUp_map_iff]
    exact hx (pl kv) (Set.mem_univ _)
  · intro hx PP _
    obtain ⟨kv, rfl⟩ := pl.surjective PP
    have := hx kv
    rw [h.comp g kv, isUniUp_map_iff] at this
    exact this

theorem chi_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : P0)
    (hg : eC g ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H) :
    ((ψ0 g : D.what₂.LLˣ) : D.what₂.LL) = ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge (eC g PP)) := by
  rw [h.chi0 g hg]
  unfold Formalism.L2.DIV.P0 LevelP.ofLocal
  dsimp only
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  exact Finset.prod_congr rfl fun PP _ => rfl

end Comparison₂

end GlobalTheory.ShareOn.WhitBase

namespace GlobalTheory.ShareOn

open GlobalTheory.ShareOn.WhitBase

open Formalism.L2.DIV in

theorem baseLevel_isWhit : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.Rows → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hR
  obtain ⟨Pg, pl, res, ψ', eC, hL, -⟩ := hR.psi
  rw [p.eGtie] at hL
  unfold HalfUnip
  generalize p.R.eG.trans p.cG = e at hL ⊢
  let ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    D.what₂.embLL.toMonoidHom.compAddChar
      ((ψ' (pl kv).1).compAddMonoidHom ((res kv).symm.toAddMonoidHom.comp (-AddMonoidHom.id _)))
  have hψ : ∀ kv c, ψ kv c = D.what₂.embLL (ψ' (pl kv).1 ((res kv).symm (-c))) := fun _ _ => rfl
  let iso := p.P.P0.equivMapOfInjective e.toMonoidHom e.injective
  have hiso : ∀ g0 : p.P.P0, ((iso g0 : p.P.P0.map e.toMonoidHom) : G0g D.nd) = e g0 := fun _ => rfl
  let lam : (p.P.P0.map e.toMonoidHom) →* ℂˣ :=
    (Units.map D.what₂.embLL.toMonoidHom).comp (p.P.ψ0⁻¹.comp iso.symm.toMonoidHom)
  have hlam : ∀ g, ((lam g : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0 (iso.symm g) : D.what₂.LLˣ) : D.what₂.LL)⁻¹ := by
    intro g
    show D.what₂.embLL (((p.P.ψ0 (iso.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = _
    rw [Units.val_inv_eq_inv_val]
  refine ⟨lam, ψ, ⟨?_, ?_, ?_⟩, ?_, ⟨0, ?_⟩⟩
  · intro kv h1
    apply hL.gen (pl kv).1 (pl kv).2
    ext x
    have h2 : ψ kv (-(res kv x)) = 1 := by rw [h1, AddChar.one_apply]
    rw [hψ, neg_neg, RingEquiv.symm_apply_apply] at h2
    rw [AddChar.one_apply]
    apply D.what₂.embLL.injective
    rw [h2, map_one]
  · intro g
    rw [Subgroup.mem_map_equiv, mem_iff_of_lvlTie hL]
    simp only [MulEquiv.apply_symm_apply]
  · intro g
    have hg0 : e (iso.symm g) = (g : G0g D.nd) := by rw [← hiso, MulEquiv.apply_symm_apply]
    have hg : eC (iso.symm g) ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ').H := (hL.p0 _).1 (iso.symm g).2
    rw [hlam, chi_of_lvlTie hL _ hg, ← Finset.prod_inv_distrib, map_prod]
    rw [← Fintype.prod_equiv pl (fun kv => D.what₂.embLL (ψ' (pl kv).1 (edgeSum supEdge (eC (iso.symm g) (pl kv))))⁻¹)
      _ (fun _ => rfl)]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← hg0, hL.comp _ kv]
    simp only [entN_map]
    rw [← map_sum, ← edgeSum_supEdge_eq, hψ, ← map_neg, RingEquiv.symm_apply_apply, AddChar.map_neg_eq_inv]
  · intro g h
    have : iso.symm ⟨_, h⟩ = g := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hlam, this, ← Units.val_inv_eq_inv_val]
    rfl
  · intro g hg v
    exact (mem_iff_of_lvlTie hL g).1 hg ⟨0, v⟩

end GlobalTheory.ShareOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.ExpTie

theorem exists_mul_eq_prW_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) {a : 𝓞 K}
    (ha : a ∈ w.asIdeal ^ (J * Formalism.L2.Col.eW w)) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ b : 𝓞 K, t * a = ((Formalism.L2.Col.prW w : ℕ) : 𝓞 K) ^ J * b := by
  have hm := (Formalism.L2.Col.algebraMap_mem_maximalIdeal_pow_iff w a (J * Formalism.L2.Col.eW w)).2 ha
  rw [mul_comm, pow_mul, ← Formalism.L2.Col.span_prW_ow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl y
  refine ⟨t, t.2, b, ?_⟩
  apply IsLocalization.injective (Formalism.L2.Col.Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors
  rw [map_mul, map_mul, hy, map_pow, map_natCast, mul_comm, mul_assoc, IsLocalization.mk'_spec]

theorem LIncl.jexpU_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : Formalism.L2.DIV.BlockDat K G Pl0} {ℓ : Formalism.L2.DIV.Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  have he : 0 < Formalism.L2.Col.eW w := Formalism.L2.Col.eW_pos w
  have hp : Formalism.EigenvalueLevelCeiling.plc w = Formalism.L2.Col.prW w :=
    Formalism.L2.Col.eq_prW_of_mem w (Formalism.EigenvalueLevelCeiling.plc_prime w) (Formalism.EigenvalueLevelCeiling.plc_mem w)
  have key : B.JexpW ℓ Z w ≤ J * Formalism.L2.Col.eW w := by
    unfold Formalism.L2.DIV.BlockDat.JexpW Formalism.L2.DIV.expW
    apply Nat.sInf_le
    intro a ha z hz
    obtain ⟨t, ht, b, htb⟩ := exists_mul_eq_prW_pow w J ha
    obtain ⟨s, hs, hsz⟩ := h z hz
    refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have e : (s * t) • (a • z) = b • (s • ((((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z)) := by
      rw [hp, smul_smul, smul_smul, smul_smul, mul_assoc, htb]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ b hsz
  refine ⟨?_, ?_⟩
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    positivity
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    rw [div_le_iff₀ (by exact_mod_cast he)]
    exact_mod_cast key

theorem jexpU_le_of_lIncl : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : Formalism.L2.DIV.BlockDat K G Pl0) (ℓ : Formalism.L2.DIV.Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => LIncl.jexpU_bounds h

end GlobalTheory.ExpTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem coinv_stab_snd (P Q R S : ℕ) (x : ℂ) : Stab (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro Z y hy
  have hcomm := (GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S).2.2.2.2
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Z f, ?_⟩
    rw [map_sub, map_smul, hcomm]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem degW_le_of_abs_le {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) (B : ℚ) (hμ : ∀ a, |μ a| ≤ B) :
    degW c μ ≤ ((p + q : ℕ) : ℚ) * (B + |c|) := by
  unfold degW
  have h : ∀ a, |shiftNu c μ a| ≤ B + |c| := by
    intro a
    rcases a with i | j
    · simp only [shiftNu]; exact (abs_sub _ _).trans (add_le_add (hμ _) le_rfl)
    · simp only [shiftNu]; exact (abs_add_le _ _).trans (add_le_add (hμ _) le_rfl)
  calc ∑ a, |shiftNu c μ a| ≤ ∑ _a : Ix p q, (B + |c|) := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Finset.card_univ, Fintype.card_sum]; ring

theorem fockCoinvariantKernel_highestWeight_admissible (P Q R S : ℕ) (x : ℂ) : AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro B
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ ⌊((R + S : ℕ) : ℚ) * (B + |cPair P Q|)⌋₊, inferInstance, ?_⟩
  intro μ hμ v hv
  obtain ⟨-, hL2, -, hw2, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  have hgood : Good (fockAct2 P Q R S) := ⟨hL2, hw2, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩
  obtain ⟨hspan, -, hK2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inl rfl))
  have hKc : KStable (fockAct2 P Q R S) (coinv P Q R S x) := fun X _ w hw => coinv_stab_snd P Q R S x X w hw
  have hv' : v ∈ (Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x) ⊓ hwSub (fockAct2 P Q R S) μ :=
    ⟨by rw [GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top]; exact Submodule.mem_top, hv⟩
  have hsplit := GlobalTheory.T.howeHighestWeight_sup_stable_le R S _ (fockAct2 P Q R S) hgood _ _ hK2 hKc μ hv'
  obtain ⟨h, hh, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  refine Submodule.add_mem_sup ?_ hc.1
  rw [mem_restrictTotalDegree]
  have hh2 : h ∈ harm2 P Q R S := by rw [← hspan]; exact hh.1
  exact (GlobalTheory.DegKeep.deg_le_of_harm hh2 hh.2).trans (Nat.floor_mono (degW_le_of_abs_le _ μ B hμ))

theorem coinv_stab_adm : ∀ (P Q R S : ℕ) (x : ℂ),
    Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) :=
  fun P Q R S x => ⟨coinv_stab_snd P Q R S x, fockCoinvariantKernel_highestWeight_admissible P Q R S x⟩

end GlobalTheory.HoweR

end
end

