import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0009
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParUniIffFlags
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {K : Type} [Field K] {r k : ℕ}

def posW (i : Fin k) : Set (Idx r k) := Set.range Sum.inl ∪ wI '' {j | j < i}

def ColW (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ i : Fin k, m *ᵥ Pi.single (wI i) 1 - Pi.single (wI i) 1 ∈
    Submodule.span K ((fun j => Pi.single j (1 : K)) '' posW (r := r) i)

theorem colW_iff (m : Matrix (Idx r k) (Idx r k) K) :
    ColW m ↔ ∀ i : Fin k, ∀ j, j ∉ posW (r := r) i → m j (wI i) = if j = wI i then 1 else 0 := by
  unfold ColW
  refine forall_congr' fun i => ?_
  rw [mem_span_single]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  have e : (m *ᵥ Pi.single (wI i) (1 : K)) j = m j (wI i) := by rw [Matrix.mulVec_single_one]; rfl
  rw [Pi.sub_apply, sub_eq_zero, e, Pi.single_apply]

theorem par_uni_iff_flags (x y : Matrix (Idx r k) (Idx r k) K) (hxy : x * y = 1) (hyx : y * x = 1) :
    Par IsUpUni x ↔ ColC x ∧ ColW x ∧ RowC y := by
  constructor
  · intro hx
    have hu : Par (fun h => IsUnit h.det) x := by
      obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
      exact ⟨h11, h33, h21, h31, h32, h, uni_unit hh, h22⟩
    obtain ⟨hC, hR⟩ := (par_iff_flags x y hxy hyx).1 hu
    refine ⟨hC, ?_, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
    rw [colW_iff]
    intro i j hj
    rcases j with a | (j | u) | c
    · exact absurd (Or.inl ⟨a, rfl⟩) hj
    · have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      have hji : ¬ j < i := fun hlt => hj (Or.inr ⟨j, hlt, rfl⟩)
      show x (wI j) (wI i) = _
      rw [show x (wI j) (wI i) = h j i from e]
      by_cases hij : j = i
      · subst hij; simp [hh.2 j, wI]
      · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) (Ne.symm hij)
        rw [hh.1 hlt]
        have : (wI j : Idx r k) ≠ wI i := by
          intro e'; apply hij; simpa [wI] using e'
        simp [wI, hij]
    · have e := congrFun (congrFun h22 (Sum.inr u)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inl (Sum.inr u))) (wI i) = 0 := e
      rw [e']; simp [wI]
    · have e := congrFun (congrFun h32 c) (Sum.inl i)
      simp only [b32, Matrix.of_apply, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inr c)) (wI i) = 0 := e
      rw [e']; simp [wI]
  · rintro ⟨hC, hW, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, -, h22⟩ := (par_iff_flags x y hxy hyx).2 ⟨hC, hR⟩
    refine ⟨h11, h33, h21, h31, h32, h, ⟨fun j i hlt => ?_, fun i => ?_⟩, h22⟩
    ·
      have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI j : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = j := by simpa [wI] using he
          subst this
          exact absurd hlt (not_lt.2 (le_of_lt hj'))
      have := (colW_iff x).1 hW i (wI j) hnot
      rw [show x (wI j) (wI i) = x (Sum.inr (Sum.inl (Sum.inl j))) (Sum.inr (Sum.inl (Sum.inl i))) from rfl] at this
      rw [this]
      have hne : (wI j : Idx r k) ≠ wI i := by
        intro e'; have : j = i := by simpa [wI] using e'
        exact absurd hlt (by rw [this]; exact lt_irrefl _)
      simp [hne]
    · have e := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI i : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = i := by simpa [wI] using he
          subst this
          exact lt_irrefl j' hj'
      have := (colW_iff x).1 hW i (wI i) hnot
      have h1 : x (wI i) (wI i) = 1 := by simpa using this
      exact h1

theorem mem_nuG_iff_flags (g : GL (Idx r k) K) :
    g ∈ nuG K r k ↔ ColFlag (g : Matrix (Idx r k) (Idx r k) K) ∧ ColW (g : Matrix (Idx r k) (Idx r k) K) ∧
      RowFlag ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) := by
  rw [colFlag_iff, rowFlag_iff]
  exact par_uni_iff_flags _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

end MassDataIdxStIm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def CoreAll : Prop :=
  ∀ (K T : Type) [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) (n : Type) [Fintype n]
    [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K),
    (∀ t, θ (s t) = (θ t).swap) → Formalism.UG.cT s J = J → IsUnit J.det →
    MassDataIdxCore.KerBack O θ s J P ∧ MassDataIdxCore.SurjCore O θ s J P

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem herm_JR : Formalism.UG.cT (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) = JR (FpX X p) X.B.I.J := by
  have hJ := X.B.I.J_herm
  unfold Formalism.UG.IsHerm at hJ
  ext i j
  have h1 := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
  simp only [JR, Matrix.map_apply, sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← h1]
  rfl

theorem unit_JR : IsUnit (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det := by
  have h1 : (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det = inclR (F := X.B.I.F) (FpX X p) X.B.I.J.det := by
    unfold JR
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr X.B.I.J_det).map _

end Loc

theorem latCore_of (hC : CoreAll) : LatCore := by
  intro D X p θ hθ P hP K hK
  obtain ⟨hKB, hSU⟩ := hC (FpX X p) (TpX X p) (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hθ (herm_JR X p) (unit_JR X p)
  have hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := hP
  let m : K →* GL (Fin X.B.I.n) (TpX X p) :=
    (HR (FpX X p) X.B.I.cm.sig X.B.I.J).subtype.comp K.subtype
  have hmem : ∀ h : K, HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J (h : HAp X p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro h
    have : (h : HAp X p) ∈ (K : Set (HAp X p)) := h.2
    rw [hK] at this
    exact this
  have hKl : ∀ h x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
      ((m h : GL (Fin X.B.I.n) (TpX X p)) : Matrix _ _ (TpX X p)) *ᵥ x ∈
        MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := by
    intro h x
    rw [← hLat, ← hLat]
    exact hmem h x
  have hon : ∀ g : GL (Fin X.B.I.n) (TpX X p), g ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) →
      (∀ x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
        (g : Matrix _ _ (TpX X p)) *ᵥ x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ
          (JR (FpX X p) X.B.I.J) P) → ∃ h, m h = g := by
    intro g hg hgs
    let x0 : HAp X p := ⟨g, hg⟩
    have hin : x0 ∈ K := by
      rw [← SetLike.mem_coe, hK]
      show g ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
      intro x
      rw [hLat, hLat]
      exact hgs x
    exact ⟨⟨_, hin⟩, rfl⟩
  obtain ⟨ψ, hψ, hker⟩ := MassDataIdxCore.latGL_gen (p.1.adicCompletionIntegers X.B.I.F) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hKB hSU ((gOf p : ℕ) : Op X p) m (fun h => (h : HAp X p).2)
    hKl hon
  refine MassDataIdxCore.reindex_gl (idxEquiv X) _ _ ψ hψ (fun h => ?_)
  rw [hker h]
  have hsm : ∀ z : Fin X.B.I.n → TpX X p,
      (((gOf p : ℕ) : Op X p) : FpX X p) • z = ((gOf p : ℕ) : Op X p) • z := fun z => rfl
  constructor
  · intro H0
    refine ⟨(hmem h), fun y hy => ?_⟩
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).1 hy)
    exact ⟨z, (hLat z).2 hz, by rw [← hsm]; exact hz'⟩
  · rintro ⟨-, H0⟩ y hy
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).2 hy)
    exact ⟨z, (hLat z).1 hz, by rw [hsm]; exact hz'⟩

theorem stRed_of_core {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : CoreAll) : StRed X p := stRed_of_parts X p hR hS (latCore_of hC)

end MassDataIdxSteps
end
end

