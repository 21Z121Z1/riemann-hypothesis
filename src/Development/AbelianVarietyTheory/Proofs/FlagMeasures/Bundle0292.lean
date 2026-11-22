import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerLatticeIdentificationCompatOfGraphEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaGraph

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem mem_gmap_iff (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap ψ Λ ↔ ψ.symm x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_map_iff (ψ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (x : S.V) :
    x ∈ U.map (ψ : S.V →ₗ[E] S.V) ↔ ψ.symm x ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, by simp⟩

theorem mem_orth_iff (U : Submodule E S.V) (x : S.V) :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  unfold orth
  simp [Submodule.mem_iInf]

theorem mem_orth_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V)
    (x : S.V) : x ∈ orth S (U.map (ψ : S.V →ₗ[E] S.V)) ↔ ψ.symm x ∈ orth S U := by
  have hi : ∀ a b, S.hT (ψ a) (ψ b) = S.hT a b := hψ
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro h y hy
    have := h (ψ y) ⟨y, hy, rfl⟩
    rw [← hi y (ψ.symm x)]
    simpa using this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [← hi y (ψ.symm x)] at this
    simpa using this

variable {T T' : E}

theorem mem_Lrep_map (ψ : S.V ≃ₗ[E] S.V) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) (x : S.V) :
    x ∈ Lrep (Formalism.HermitianLatticesTheory.gmap ψ Λ) G ↔ ψ.symm x ∈ Lrep Λ F := by
  unfold Lrep
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_orth_map ψ hψ]

theorem gmap_eq (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap ψ Λ = Λ.map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [mem_gmap_iff, Submodule.mem_map_equiv]
  rfl

theorem XLam_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V)
    (F G : LFlag S r T) (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G) :
    XLam (Formalism.HermitianLatticesTheory.gmap ψ Λ) G = (XLam Λ F).map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
  ext x
  rw [Submodule.mem_map_equiv]
  unfold XLam
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_gmap_iff, toO, toO, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, ← hF, mem_map_iff]
  rfl

theorem mem_NgX_map (ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F G : LFlag S r T) (F' G' : LFlag S r T') (hF : (Xsp F).map (ψ : S.V →ₗ[E] S.V) = Xsp G)
    (hF' : (Xsp F').map (ψ : S.V →ₗ[E] S.V) = Xsp G') (x : S.V) :
    x ∈ NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' ↔ ψ.symm x ∈ NgX Λ g F F' := by
  have h : NgX (Formalism.HermitianLatticesTheory.gmap ψ Λ) g G G' =
      (NgX Λ g F F').map (ψ.restrictScalars (𝓞 E) : S.V →ₗ[𝓞 E] S.V) := by
    unfold NgX
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', XLam_map ψ Λ F G hF,
      XLam_map ψ Λ F' G' hF', gmap_eq]
  rw [h, Submodule.mem_map_equiv]
  rfl

end Gen

end GlobalTheory.IotaGraph

namespace GlobalTheory.IotaGraph

section Dv

variable {D : D7} {T T' : D.host.E}

theorem mem_graph_iff (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {x' l : (VS D).V} (hx' : x' ∈ Lrep Λ F') (hl : l ∈ Lrep Λ F) :
    (x', l) ∈ (gdat F F' Λ).2.2 ↔ l - x' ∈ NgX Λ (gS D) F F' := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l₀, hl₀, h1, h2, h3⟩
    have hx'Λ : x' ∈ Λ := (Submodule.mem_inf.1 hx').1
    have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
    have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
    have hl₀Λ : l₀ ∈ Λ := (Submodule.mem_inf.1 hl₀).1
    have a1 : x' - l' ∈ XLam Λ F' := Submodule.mem_inf.2 ⟨Λ.sub_mem hx'Λ hl'Λ, h1⟩
    have a2 : l - l₀ ∈ XLam Λ F := Submodule.mem_inf.2 ⟨Λ.sub_mem hlΛ hl₀Λ, h2⟩
    have b1 : x' - l' ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_right a1
    have b2 : l - l₀ ∈ NgX Λ (gS D) F F' := by
      unfold NgX; exact Submodule.mem_sup_left (Submodule.mem_sup_right a2)
    have e : l - x' = (l - l₀) + (l₀ - l') - (x' - l') := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ b2 h3) b1
  · intro h
    exact ⟨x', hx', l, hl, by simp, by simp, h⟩

theorem mem_graph_of_sub (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F)
    (hp : p ∈ (gdat F F' Λ).2.2) : q ∈ (gdat F F' Λ).2.2 := by
  simp only [gdat, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨l', hl', l, hl, k1, k2, k3⟩ := hp
  refine ⟨l', hl', l, hl, ?_, ?_, k3⟩
  · have e : q.1 - l' = (q.1 - p.1) + (p.1 - l') := by abel
    rw [e]; exact Submodule.add_mem _ h1 k1
  · have e : q.2 - l = (q.2 - p.2) + (p.2 - l) := by abel
    rw [e]; exact Submodule.add_mem _ h2 k2

theorem mem_graph_congr (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D)
    {p q : (VS D).V × (VS D).V} (h1 : q.1 - p.1 ∈ Xsp F') (h2 : q.2 - p.2 ∈ Xsp F) :
    p ∈ (gdat F F' Λ).2.2 ↔ q ∈ (gdat F F' Λ).2.2 := by
  refine ⟨mem_graph_of_sub F F' Λ h1 h2, mem_graph_of_sub F F' Λ ?_ ?_⟩
  · rw [← neg_sub]; exact Submodule.neg_mem _ h1
  · rw [← neg_sub]; exact Submodule.neg_mem _ h2

theorem mem_graph_map (ψ : GV D) (hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T')
    (hF : (Xsp F).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G)
    (hF' : (Xsp F').map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G') (Λ : LV D) (x y : (VS D).V) :
    (x, y) ∈ (gdat F F' Λ).2.2 ↔ (ψ x, ψ y) ∈ (gdat G G' (Formalism.HermitianLatticesTheory.gmap ψ Λ)).2.2 := by
  simp only [gdat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ l', ?_, ψ l, ?_, ?_, ?_, ?_⟩
    · rw [mem_Lrep_map ψ hψ Λ F' G' hF']; simpa using hl'
    · rw [mem_Lrep_map ψ hψ Λ F G hF]; simpa using hl
    · rw [← hF', mem_map_iff]; simpa using h1
    · rw [← hF, mem_map_iff]; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF']; simpa using h3
  · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
    refine ⟨ψ.symm l', (mem_Lrep_map ψ hψ Λ F' G' hF' l').1 hl', ψ.symm l,
      (mem_Lrep_map ψ hψ Λ F G hF l).1 hl, ?_, ?_, ?_⟩
    · rw [← hF', mem_map_iff] at h1; simpa using h1
    · rw [← hF, mem_map_iff] at h2; simpa using h2
    · rw [mem_NgX_map ψ Λ (gS D) F G F' G' hF hF'] at h3; simpa using h3

end Dv

end GlobalTheory.IotaGraph

namespace GlobalTheory

open GlobalTheory.IotaGraph

theorem iotaCompat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (VS D) D.R.rS T) (P₁ P₂ B' : LFlag (VS D) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  intro D T T' F₀ B P₁ P₂ B' Λ ψ₀ ψ₁ β h0 h1 hF0 hF1 hP1 hP2 hgr hβ hβΛ hβP hml hmx x' hx' l hl
  have hc : ∀ y, ψ₁ ((ψ₁⁻¹ * ψ₀) y) = ψ₀ y := fun y => ψ₁.apply_symm_apply (ψ₀ y)

  have hβx : β x' ∈ Lrep Λ P₂ := by
    have := (mem_Lrep_map (S := VS D) β hβ Λ P₁ P₂ hβP (β x')).2 (by simpa using hx')
    rwa [hβΛ] at this
  have e1 := mem_graph_iff F₀ P₁ Λ hx' hl
  have e2 := mem_graph_map ψ₀ h0 F₀ B P₁ B' hF0 hP1 Λ x' l
  have e3 := mem_graph_map ψ₁ h1 F₀ B P₂ B' hF1 hP2 Λ ((ψ₁⁻¹ * ψ₀) x') ((ψ₁⁻¹ * ψ₀) l)
  rw [hc, hc] at e3
  have e4 := mem_graph_congr F₀ P₂ Λ (p := ((ψ₁⁻¹ * ψ₀) x', (ψ₁⁻¹ * ψ₀) l)) (q := (β x', l))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hmx x' hx'))
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hml l hl))
  have e5 := mem_graph_iff F₀ P₂ Λ hβx hl
  rw [← e1, ← e5, e2, hgr, ← e3, e4]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCount
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem finrank_le_card_of_isotropic {n : ℕ} (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) (b : Bool) :
    Module.finrank ℂ V ≤ (univ.filter fun a => ε a = b).card := by

  let f : V →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {a // ε a = b} → Fin n)) ∘ₗ V.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∀ a, ε a = b → (x : Fin n → ℂ) a = 0 := fun a ha => by
      simpa [f] using congrFun hx ⟨a, ha⟩
    have hterm : ∀ a, star ((x : Fin n → ℂ) a) * ((if ε a then (1 : ℂ) else -1) * (x : Fin n → ℂ) a)
        = (if b then (-1 : ℂ) else 1) * ((Complex.normSq ((x : Fin n → ℂ) a) : ℝ) : ℂ) := by
      intro a
      by_cases ha : ε a = b
      · simp [hx0 a ha]
      · have hb : ε a = !b := by cases h1 : ε a <;> cases b <;> simp_all
        rw [Complex.normSq_eq_conj_mul_self, hb]
        cases b <;> simp [Complex.star_def] <;> ring
    have h0 := hV x x.2
    simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, hterm,
      ← Finset.mul_sum] at h0
    have hc : (if b then (-1 : ℂ) else 1) ≠ 0 := by cases b <;> simp
    have hsum : (∑ a, Complex.normSq ((x : Fin n → ℂ) a) : ℝ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hc
      exact_mod_cast this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp hsum
    ext a
    simpa using hall a (Finset.mem_univ a)
  calc Module.finrank ℂ V ≤ Module.finrank ℂ ({a // ε a = b} → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card {a // ε a = b} := Module.finrank_fintype_fun_eq_card ℂ
    _ = (univ.filter fun a => ε a = b).card := Fintype.card_subtype _

private theorem finrank_last_eq_sum_of_finrank_succ {n : ℕ} : ∀ (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) →
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  intro a
  induction a with
  | zero =>
    intro j W h0 _
    simp [show Fin.last 0 = (0 : Fin 1) from rfl, h0]
  | succ a ih =>
    intro j W h0 hstep
    have hprev := ih (fun i => j i.castSucc) (fun i => W i.castSucc) (by simpa using h0)
      (fun i => by have hs := hstep i.castSucc; rw [Fin.succ_castSucc] at hs; exact hs)
    rw [Fin.sum_univ_castSucc, ← hprev, ← Fin.succ_last, hstep (Fin.last a)]

theorem finrank_last_eq_sum {n : ℕ} {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : IsIsoFlag ε j W) :
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i :=
  finrank_last_eq_sum_of_finrank_succ a j W h.1 h.2.2.1

private theorem sq_sum_eq_sum_sq_add_two_mul_sum_lt' {a : ℕ} (j : Fin a → ℕ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
  have split : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsym : ∑ i, ∑ k, (if k < i then j i * j k else 0) = ∑ i, ∑ k, (if i < k then j i * j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hexp : ∑ i, ∑ k, j i * j k = ∑ i, ∑ k, ((if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => split i k
  have hdiag : ∑ i, ∑ k, (if i = k then j i * j k else 0) = ∑ i, j i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [sq, Finset.sum_mul_sum, hexp]
  simp only [Finset.sum_add_distrib]
  rw [hsym, hdiag]
  simp only [Finset.sum_filter]
  ring

theorem flag_dims : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  intro n ε a j W h p q hp hq
  have hpq : p + q = n := by
    rw [← hp, ← hq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this

  have hV : ∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0 :=
    fun x hx => h.2.2.2 x hx x hx
  have hS := finrank_last_eq_sum h
  have hSp : ∑ i, j i ≤ p := by
    rw [← hS, ← hp]; exact finrank_le_card_of_isotropic ε _ hV true
  have hSq : ∑ i, j i ≤ q := by
    rw [← hS, ← hq]; exact finrank_le_card_of_isotropic ε _ hV false
  have hsq := sq_sum_eq_sum_sq_add_two_mul_sum_lt' j
  subst hpq
  simp only [dimN]
  set S := ∑ i, j i
  set X := ∑ i, j i ^ 2
  set T := ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k
  obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hSp
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hSq
  have e1 : S + P + (S + Q) - 2 * S = P + Q := by omega
  have e2 : S + P - S = P := by omega
  have e3 : S + Q - S = Q := by omega
  rw [e1, e2, e3]
  refine ⟨by trivial, ?_, ?_⟩ <;> nlinarith [hsq]

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeeps
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLevi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem iwasawa_shift_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (M : Set G) (μM μK : Measure G) [SFinite μK] (δ φ ψ : G → ENNReal)
    (hδ : Measurable δ) (hφ : Measurable φ) (hψ : Measurable ψ) (hM : μM Mᶜ = 0) (l : G)
    (h1 : μM.map (fun g => g * l) = μM) (h2 : μK.map (fun g => l * g) = μK)
    (h3 : ∀ m ∈ M, δ (m * l) = δ m) (u : G) :
    ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM
      = ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM := by
  have hae : ∀ᵐ m ∂μM, m ∈ M := by rw [ae_iff]; exact hM

  have hK : ∀ m, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK
      = ∫⁻ k, φ (u * (m * l⁻¹) * k) * ψ k ∂μK := by
    intro m
    conv_rhs => rw [← h2, show (fun g : G => l * g) = ⇑(MeasurableEquiv.mulLeft l) from rfl,
      lintegral_map_equiv]
    simp [mul_assoc]
  simp_rw [hK]

  conv_rhs => rw [← h1, show (fun g : G => g * l) = ⇑(MeasurableEquiv.mulRight l) from rfl,
    lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hae] with m hm
  simp [mul_assoc, h3 m hm]

theorem iwasawa_unfold_lintegral : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  intro G _ _ _ M L μN μM μK νL _ _ _ _ δ φ ψ hδ hφ hψ hM hL h1 h2 h3
  have hLae : ∀ᵐ l ∂νL, l ∈ L := by rw [ae_iff]; exact hL

  have hH : Measurable fun p : G × G × G =>
      δ p.2.1 * ∫⁻ k, φ (p.1 * p.2.1 * k) * ψ (p.2.2 * k) ∂μK := by
    refine Measurable.mul (hδ.comp measurable_snd.fst) ?_
    exact Measurable.lintegral_prod_right'
      (f := fun q : (G × G × G) × G => φ (q.1.1 * q.1.2.1 * q.2) * ψ (q.1.2.2 * q.2)) (by fun_prop)
  have hX : Measurable fun p : G × G =>
      ∫⁻ m, δ m * ∫⁻ k, φ (p.1 * m * k) * ψ (p.2 * k) ∂μK ∂μM :=
    Measurable.lintegral_prod_right' (f := fun q : (G × G) × G =>
        δ q.2 * ∫⁻ k, φ (q.1.1 * q.2 * k) * ψ (q.1.2 * k) ∂μK)
      (hH.comp (f := fun q : (G × G) × G => (q.1.1, q.2, q.1.2)) (by fun_prop))

  have step1 : ∀ u m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
      = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
    intro u m
    have hg : Measurable fun l => ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK :=
      Measurable.lintegral_prod_right' (f := fun q : G × G => φ (u * m * q.2) * ψ (q.1 * q.2))
        (by fun_prop)
    calc δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
        = δ m * ∫⁻ k, ∫⁻ l, φ (u * m * k) * ψ (l * k) ∂νL ∂μK := by
          congr 1
          exact lintegral_congr fun k => (lintegral_const_mul _ (hψ.comp (measurable_mul_const k))).symm
      _ = δ m * ∫⁻ l, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
          congr 1
          exact lintegral_lintegral_swap (by
            exact (show Measurable fun q : G × G => φ (u * m * q.1) * ψ (q.2 * q.1) by fun_prop).aemeasurable)
      _ = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := (lintegral_const_mul _ hg).symm
  have step2 : ∀ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM
      = ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL := by
    intro u
    calc _ = ∫⁻ m, ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL ∂μM :=
          lintegral_congr fun m => step1 u m
      _ = _ := lintegral_lintegral_swap (by
          exact (hH.comp (f := fun q : G × G => (u, q.1, q.2)) (by fun_prop)).aemeasurable)

  have key : ∀ᵐ l ∂νL, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN
      = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN := by
    filter_upwards [hLae] with l hl
    exact lintegral_congr fun u =>
      (iwasawa_shift_lintegral M μM μK δ φ ψ hδ hφ hψ hM l (h1 l hl) (h2 l hl) (h3 l hl) u).symm
  calc νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN
      = ∫⁻ _l, (∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN) ∂νL := by
        rw [lintegral_const]; exact mul_comm _ _
    _ = ∫⁻ l, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN ∂νL :=
        lintegral_congr_ae (key.mono fun _ hl => hl.symm)
    _ = ∫⁻ u, ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL ∂μN :=
        (lintegral_lintegral_swap (by exact hX.aemeasurable)).symm
    _ = _ := lintegral_congr fun u => (step2 u).symm

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulThetaStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  first | exact @GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | exact GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | (intros; apply GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInvStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTermWeight_eq_character_mul_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r k : ℕ) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : WCoord P S) (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t → ∀ m m' : S.GLV, (∀ b, c.e (t.f b) = m (S.f b)) → (∀ b, c.e (t.f' b) = m' (S.f' b)) → LocNG.om P t = S.psi m * (S.psi' m')⁻¹ := by
  first | exact @GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv | exact GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv | (intros; apply GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  first | exact @GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | exact GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | (intros; apply GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant <;> assumption)
end

