import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewHermitianOfUnitaryExp
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.KD

variable {n : ℕ}

private abbrev tt (n : ℕ) : Fin n → Bool := fun _ => true

private abbrev UU (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := PI.UpqRep.UJset (tt n)

private theorem jm_tt : Formalism.REAL.Jm (tt n) = 1 := by
  simp [Formalism.REAL.Jm]

private theorem mem_UU {g : Matrix (Fin n) (Fin n) ℂ} : g ∈ UU n ↔ g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show Formalism.REAL.inUJ (tt n) g ↔ _
  unfold Formalism.REAL.inUJ
  rw [jm_tt, Matrix.mul_one, Matrix.star_eq_conjTranspose]

open scoped Norms.Operator in
private theorem skew_hermitian_of_unitary_exp (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ) : Xᴴ = -X := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ∀ (t : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • Y = t • Y := fun t Y => by
    ext a b
    simp
  have e : ∀ t : ℝ, NormedSpace.exp (t • Xᴴ) = NormedSpace.exp (t • (-X)) := by
    intro t
    have hu := h t
    have h1 : NormedSpace.exp (t • Xᴴ) = star (NormedSpace.exp ((t : ℂ) • X)) := by
      rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul]
      simp [hsm]
    have h2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (t • (-X)) = 1 := by
      rw [hsm, smul_neg, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right t).neg_right]
      simp
    have h3 := Unitary.star_mul_self_of_mem hu
    calc NormedSpace.exp (t • Xᴴ) = star (NormedSpace.exp ((t : ℂ) • X)) * 1 := by rw [h1, mul_one]
      _ = star (NormedSpace.exp ((t : ℂ) • X)) * (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (t • (-X))) := by
        rw [h2]
      _ = NormedSpace.exp (t • (-X)) := by rw [← mul_assoc, h3, one_mul]
  have d1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ (0 : ℝ)
  have d2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  have hu := (d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (e t).symm)).unique d2
  simpa using hu

private theorem skew_of (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.inG (tt n) X := by
  show Xᴴ * Formalism.REAL.Jm (tt n) + Formalism.REAL.Jm (tt n) * X = 0
  rw [jm_tt, Matrix.mul_one, Matrix.one_mul, skew_hermitian_of_unitary_exp X h]
  simp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Sub

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def rs (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (W : Submodule ℂ H)
    (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (g : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  ((σ g).comp W.subtypeL).codRestrict W (fun v => hW g v v.2)

private theorem rs_coe (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (W : Submodule ℂ H)
    (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (g : Matrix (Fin n) (Fin n) ℂ) (v : W) :
    ((rs σ W hW g v : W) : H) = σ g v := rfl

private theorem rs_rep {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    (W : Submodule ℂ H) (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) : PI.UpqRep.IsURepOn (UU n) (rs σ W hW) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext v
    rw [rs_coe, hσ.1.1]
    rfl
  · ext v
    rw [rs_coe, hσ.1.2 a ha b hb]
    rfl
  · exact hσ.2.1 g hg (v : H)
  · exact (Topology.IsInducing.subtypeVal.continuousOn_iff).2 (hσ.2.2 (v : H))

private theorem rs_smooth {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Hm : Matrix (Fin n) (Fin n) ℂ}
    (W : Submodule ℂ H) (hW : ∀ g, ∀ v ∈ W, σ g v ∈ W) (v : W)
    (hv : v ∈ PI.PhMeasCore.smoothVecs Hm (rs σ W hW)) : (v : H) ∈ PI.PhMeasCore.smoothVecs Hm σ := by
  intro g₀ hg
  obtain ⟨U, F, hU, hg0, hF, h⟩ := hv g₀ hg
  refine ⟨U, fun g => ((F g : W) : H), hU, hg0, ?_, fun g hgU hgH => congrArg Subtype.val (h g hgU hgH)⟩
  exact (W.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF

private theorem inner_rep {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UU n) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), fun v => hσ.2.1 g hg v⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

private theorem orth_stable {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsURepOn (UU n) σ)
    (hz : ∀ g, g ∉ UU n → σ g = 0) {S : Submodule ℂ H} (hS : ∀ g ∈ UU n, ∀ v ∈ S, σ g v ∈ S) :
    ∀ g, ∀ v ∈ Sᗮ, σ g v ∈ Sᗮ := by
  intro g v hv
  by_cases hg : g ∈ UU n
  · have hg' := mem_UU.1 hg
    have hs : star g ∈ UU n := mem_UU.2 (Unitary.star_mem hg')
    rw [Submodule.mem_orthogonal]
    intro s hs'
    have h1 : σ (star g) (σ g v) = v := by
      have := hσ.1.2 _ hs _ hg
      rw [Unitary.star_mul_self_of_mem hg', hσ.1.1] at this
      exact (congrArg (fun T : H →L[ℂ] H => T v) this).symm
    rw [← inner_rep hσ hs, h1]
    exact (Submodule.mem_orthogonal _ _).1 hv _ (hS _ hs _ hs')
  · rw [hz g hg]
    exact Sᗮ.zero_mem

private theorem top_of [FiniteDimensional ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsURepOn (UU n) σ) (hz : ∀ g, g ∉ UU n → σ g = 0) {S : Submodule ℂ H}
    (hS : ∀ g ∈ UU n, ∀ v ∈ S, σ g v ∈ S)
    (hmem : ∀ v, v ∈ S ↔ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (tt n)) σ) : S = ⊤ := by
  by_contra hne
  have hT : Sᗮ ≠ ⊥ := fun h => hne ((Submodule.orthogonal_eq_bot_iff).1 h)
  obtain ⟨W, ⟨hW0, hWT, hWs⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ H)).has_min
    {W | W ≠ ⊥ ∧ W ≤ Sᗮ ∧ ∀ g, ∀ v ∈ W, σ g v ∈ W} ⟨Sᗮ, hT, le_rfl, orth_stable hσ hz hS⟩
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hirr : PI.UpqRep.IsIrredOn (UU n) (rs σ W hWs) := by
    intro S' _ hS'
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    refine Or.inr ?_
    have hle : S'.map W.subtype ≤ W := Submodule.map_subtype_le W S'
    have hst : ∀ g, ∀ v ∈ S'.map W.subtype, σ g v ∈ S'.map W.subtype := by
      intro g v hv
      by_cases hg : g ∈ UU n
      · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
        exact Submodule.mem_map.2 ⟨_, hS' g hg x hx, rfl⟩
      · rw [hz g hg]
        exact Submodule.zero_mem _
    have hne' : S'.map W.subtype ≠ ⊥ := fun h => h0 (Submodule.map_injective_of_injective W.injective_subtype (h.trans (Submodule.map_bot _).symm))
    have heq : S'.map W.subtype = W := by
      by_contra hc
      exact hmin _ ⟨hne', hle.trans hWT, hst⟩ (lt_of_le_of_ne hle hc)
    rw [eq_top_iff]
    intro w _
    have : (w : H) ∈ S'.map W.subtype := by
      rw [heq]
      exact w.2
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.1 this
    rwa [← Subtype.ext hxw]
  have hWS : W ≤ S := by
    intro v hv
    refine (hmem v).2 (rs_smooth W hWs ⟨v, hv⟩ ?_)
    exact CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n (tt n) W (rs σ W hWs) (rs_rep hσ W hWs) hirr ⟨v, hv⟩
      ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  apply hW0
  rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot S]
  exact le_inf hWS hWT

end Sub

private def sgm (E : KMod n) (g : Matrix (Fin n) (Fin n) ℂ) : E.V →L[ℂ] E.V := by
  classical exact if h : g ∈ Matrix.unitaryGroup (Fin n) ℂ then E.ρ ⟨g, h⟩ else 0

private theorem sgm_coe (E : KMod n) (k : UK n) : sgm E k.1 = E.ρ k := by
  simp only [sgm]
  rw [dif_pos k.2]

private theorem sgm_zero (E : KMod n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∉ UU n) : sgm E g = 0 := by
  simp only [sgm]
  rw [dif_neg (fun h => hg (mem_UU.2 h))]

private theorem sgm_rep (E : KMod n) : PI.UpqRep.IsURepOn (UU n) (sgm E) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · exact (sgm_coe E 1).trans (map_one E.ρ)
  · have ha' := mem_UU.1 ha
    have hb' := mem_UU.1 hb
    have h := sgm_coe E (⟨a, ha'⟩ * ⟨b, hb'⟩)
    rw [map_mul, ← sgm_coe E ⟨a, ha'⟩, ← sgm_coe E ⟨b, hb'⟩] at h
    exact h
  · rw [show sgm E g = E.ρ ⟨g, mem_UU.1 hg⟩ from sgm_coe E ⟨g, mem_UU.1 hg⟩]
    exact E.iso _ v
  · rw [continuousOn_iff_continuous_restrict]
    have e : (fun u : UU n => sgm E u.1 v) = fun u : UU n => E.ρ ⟨u.1, mem_UU.1 u.2⟩ v := by
      funext u
      exact congrArg (fun T : E.V →L[ℂ] E.V => T v) (sgm_coe E ⟨u.1, mem_UU.1 u.2⟩)
    show Continuous (fun u : UU n => sgm E u.1 v)
    rw [e]
    exact (E.cont.comp (Continuous.subtype_mk continuous_subtype_val _)).clm_apply continuous_const

end UpperTheory.RealTr.KD

open UpperTheory.RealTr.KD in
theorem UpperTheory.RealTr.kDer :
    ∀ (n : ℕ) (E : KMod n), ∃ (σ : UK n →* (E.V →ₗ[ℂ] E.V)) (F : Fin n → Fin n → Module.End ℂ E.V), (∀ k v, σ k v = E.ρ k v) ∧ UF F ∧ IsDerivK σ F := by
  intro n E
  obtain ⟨S, F, hM⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hSmMod n (tt n) E.V (sgm E) (sgm_rep E)
  obtain rfl : S = ⊤ := top_of (sgm_rep E) (fun g hg => sgm_zero E hg) (fun g hg v hv => hM.stab g hg v hv) hM.mem
  let σ' : UK n →* (E.V →ₗ[ℂ] E.V) :=
    { toFun := fun k => (E.ρ k : E.V →ₗ[ℂ] E.V)
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  let F' : Fin n → Fin n → Module.End ℂ E.V := fun a b =>
    (⊤ : Submodule ℂ E.V).subtype ∘ₗ F a b ∘ₗ LinearMap.codRestrict ⊤ LinearMap.id (fun _ => trivial)
  have hF' : ∀ a b x, F' a b x = ((F a b ⟨x, trivial⟩ : (⊤ : Submodule ℂ E.V)) : E.V) := fun _ _ _ => rfl
  refine ⟨σ', F', fun _ _ => rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b c d
    ext x
    have h := congrArg (fun T : Module.End ℂ (⊤ : Submodule ℂ E.V) => ((T ⟨x, trivial⟩ : (⊤ : Submodule ℂ E.V)) : E.V)) (hM.gl a b c d)
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simpa [h1, h2, hF', Module.End.mul_apply] using h
  · intro a b x y
    have h := hM.unit a b ⟨x, trivial⟩ ⟨y, trivial⟩
    simpa [Formalism.REAL.sgn, hF'] using h
  · intro k x y
    exact (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V).inner_map_map x y
  · intro v
    refine ⟨⊤, inferInstance, trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial, ?_⟩
    intro X γ hγ w _
    have hX : Formalism.REAL.inG (tt n) X := skew_of X (fun t => by rw [← hγ t]; exact (γ t).2)
    have h := hM.real X hX ⟨w, trivial⟩
    have e : (fun t : ℝ => σ' (γ t) w) = fun t : ℝ => sgm E (NormedSpace.exp ((t : ℂ) • X)) w := by
      funext t
      rw [← hγ t, sgm_coe]
      rfl
    rw [e]
    exact h
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnRel
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem tri {A : Type} [Ring A] (x y z p q : A) (h1 : y * z + z * y = p)
    (h2 : x * z + z * x = q) : x * y * z - z * (x * y) = x * p - q * y := by
  rw [← h1, ← h2]
  noncomm_ring

private theorem leib {A : Type} [Ring A] (X u v : A) :
    X * (u * v) - u * v * X = (X * u - u * X) * v + u * (X * v - v * X) := by
  noncomm_ring

private theorem spn_comm {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (a b d e : Fin n) :
    spn c a b * c d e - c d e * spn c a b =
      (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have hsum : spn c a b * c d e - c d e * spn c a b =
      ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b)) := by
    unfold spn
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [hsum]
  have hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) =
      c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b := by
    intro f
    exact tri _ _ _ _ _ (hc f b d e) (hc a f d e)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hbd : b = d
    · simp [hbd]
    · simp [hbd]
  · by_cases hea : e = a
    · subst hea
      simp
    · have : ∀ f : Fin n, ¬ (f = d ∧ a = e) := fun f h => hea h.2.symm
      simp [this, hea]

theorem UpperTheory.RealTr.spnRel :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A), Clif c → GlRel (spn c) ∧
      ∀ a b d e, spn c a b * c d e - c d e * spn c a b = (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  intro n A _ _ c hc
  refine ⟨?_, fun a b d e => spn_comm c hc a b d e⟩
  intro a b g h
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have expand : ∀ X : A, X * spn c g h - spn c g h * X =
      ∑ f, (X * (c g f * c f h) - c g f * c f h * X) := by
    intro X
    unfold spn
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [expand]
  simp_rw [leib, spn_comm c hc]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  unfold spn
  by_cases hbg : b = g <;> by_cases hha : h = a
  · subst hbg
    subst hha
    simp
  · simp [hbg, hha, Ne.symm hha]
  · simp [hbg, hha, Ne.symm hbg]
    abel
  · simp [hbg, hha, Ne.symm hbg, Ne.symm hha]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trace_restrict_sup_disjoint {V : Type} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (S S' : Submodule ℂ V) (hF : FiniteDimensional ℂ S) (hF' : FiniteDimensional ℂ S')
    (hd : Disjoint S S') (hS : ∀ x ∈ S, f x ∈ S) (hS' : ∀ x ∈ S', f x ∈ S')
    (hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S') :
    LinearMap.trace ℂ ↥(S ⊔ S') (f.restrict hT) =
      LinearMap.trace ℂ S (f.restrict hS) + LinearMap.trace ℂ S' (f.restrict hS') := by
  let φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S') :=
    ((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by
      simpa using Submodule.add_mem_sup p.1.2 p.2.2))
  have hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have h0 : (a : V) + (b : V) = 0 := by simpa [hφ] using congrArg Subtype.val h
    have ha : (a : V) ∈ S' := by
      have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact S'.neg_mem b.2
    have ha0 : (a : V) = 0 := (Submodule.disjoint_def.1 hd) _ a.2 ha
    have hb0 : (b : V) = 0 := by simpa [ha0] using h0
    ext <;> simp [ha0, hb0]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩
  let e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S') := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := fun p => hφ p
  have hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS')) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨p, rfl⟩ := e.surjective x
    have hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) =
        e ((f.restrict hS).prodMap (f.restrict hS') p) := by
      simp [LinearEquiv.conj_apply]
    rw [hc]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, he, he, map_add]
    rfl
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem UpperTheory.RealTr.trAdd :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V),
      (∀ S S' : Submodule ℂ V, FiniteDimensional ℂ S → FiniteDimensional ℂ S' → Disjoint S S' → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S', f x ∈ S') →
        trOn (S ⊔ S') f = trOn S f + trOn S' f) ∧
      (∀ (S : Submodule ℂ V) (g : Module.End ℂ V) (c : ℂ), (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, g x ∈ S) →
        trOn S (f + g) = trOn S f + trOn S g ∧ trOn S (c • f) = c * trOn S f ∧ ((∀ x ∈ S, f x = g x) → trOn S f = trOn S g)) ∧
      (∀ (S S' : Submodule ℂ V) (g : Module.End ℂ V), FiniteDimensional ℂ S → FiniteDimensional ℂ S' → (∀ x ∈ S, f x ∈ S') → (∀ x ∈ S', g x ∈ S) →
        trOn S (g * f) = trOn S' (f * g)) ∧
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → trOn S (1 : Module.End ℂ V) = Module.finrank ℂ S := by
  intro V _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hF hF' hd hS hS'
    have hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S' := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hS a ha) (hS' b hb)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos hT, dif_pos hS, dif_pos hS']
    exact trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT
  · intro S g c hf hg
    have hfg : ∀ x ∈ S, (f + g) x ∈ S := fun x hx => S.add_mem (hf x hx) (hg x hx)
    have hcf : ∀ x ∈ S, (c • f) x ∈ S := fun x hx => S.smul_mem c (hf x hx)
    refine ⟨?_, ?_, ?_⟩
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hfg, dif_pos hf, dif_pos hg, ← map_add]
      congr 1
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hcf, dif_pos hf]
      have : (c • f).restrict hcf = c • f.restrict hf := by ext x; simp
      rw [this, map_smul, smul_eq_mul]
    · intro he
      unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hf, dif_pos hg]
      congr 1
      ext x
      simp [he x x.2]
  · intro S S' g hF hF' hf hg
    have h1 : ∀ x ∈ S, (g * f) x ∈ S := fun x hx => hg _ (hf x hx)
    have h2 : ∀ x ∈ S', (f * g) x ∈ S' := fun x hx => hf _ (hg x hx)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1, dif_pos h2]
    let a : S →ₗ[ℂ] S' := f.restrict hf
    let b : S' →ₗ[ℂ] S := g.restrict hg
    have e1 : (g * f).restrict h1 = b ∘ₗ a := by ext x; rfl
    have e2 : (f * g).restrict h2 = a ∘ₗ b := by ext x; rfl
    rw [e1, e2]
    exact LinearMap.trace_comp_comm' a b
  · intro S hF
    have h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S := fun x hx => hx
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1]
    have : (1 : Module.End ℂ V).restrict h1 = LinearMap.id := by ext x; rfl
    rw [this, LinearMap.trace_id]
end
end

