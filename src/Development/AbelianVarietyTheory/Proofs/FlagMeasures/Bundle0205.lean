import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealMatrixMemBesselUnipotentOfFrame
section
open Matrix

noncomputable section
open Formalism.HermitianLatticeCounting.S6 Formalism.QuantumDeterminants GlobalTheory.DegVol.RealMat

namespace GlobalTheory.DegVol.FrameUnip

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {k r : ℕ} {σ : K →+* ℂ} {Φ : V → Fin (2 * r + k + 1) → ℂ}

theorem phi_zero' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) : Φ 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem phi_sub' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (x y : V) : Φ (x - y) = Φ x - Φ y := by
  have := h.1 (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem phi_sum' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {α : Type} (s : Finset α) (f : α → V) :
    Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phi_zero' h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem span_ind' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (P : (Fin (2 * r + k + 1) → ℂ) → Prop) (h0 : ∀ x, P (Φ x))
    (ha : ∀ u v, P u → P v → P (u + v)) (hs : ∀ (c : ℂ) u, P u → P (c • u)) (u : Fin (2 * r + k + 1) → ℂ) : P u := by
  have hu : u ∈ Submodule.span ℂ (Set.range Φ) := by rw [h.2.2.2]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact h0 y
  | zero => rw [← phi_zero' h]; exact h0 0
  | add x y _ _ hx hy => exact ha _ _ hx hy
  | smul c x _ hx => exact hs _ _ hx

theorem mem_UH' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (e : ∀ x y, herm (Hpk k r) (m *ᵥ Φ x) (m *ᵥ Φ y) = herm (Hpk k r) (Φ x) (Φ y)) : m ∈ UH (Hpk k r) := by
  have h1 : ∀ u w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w := by
    intro u
    refine span_ind' h (fun u => ∀ w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w) (fun x => ?_)
      (fun u v hu hv w => by rw [mulVec_add, herm_add_left, herm_add_left, hu, hv])
      (fun c u hu w => by rw [mulVec_smul, herm_smul_left, herm_smul_left, hu]) u
    exact span_ind' h _ (e x) (fun u v hu hv => by rw [mulVec_add, herm_add_right, herm_add_right, hu, hv])
      (fun c u hu => by rw [mulVec_smul, herm_smul_right, herm_smul_right, hu])
  ext i j
  exact (herm_bvec _ i j).symm.trans (by rw [← herm_mulVec, h1, herm_bvec])

theorem coord_span (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {e : Fin r → V} {ρ : Fin r → ℂ}
    (he : ∀ a, Φ (e a) = ρ a • bvec (eI k r a)) {S : Set (Fin r)} (i : Fin (2 * r + k + 1))
    (hS : ∀ b ∈ S, b.val < i.val) {y : V} (hy : y ∈ Submodule.span K (e '' S)) : Φ y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' := hS b hb
    have : i ≠ eI k r b := fun e => by
      have := congrArg Fin.val e
      simp only [eI] at this; omega
    simp [he, bvec, this]
  | zero => rw [phi_zero' h]; rfl
  | add x y _ _ hx hy => rw [h.1, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [h.2.1, Pi.smul_apply, hx, smul_zero]

theorem mem_Nset : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro K V _ _ _ _ H k r σ Φ h e f ρ ρ' hρ hρ' he hf hef m hm h2 h3 n hn
  refine ⟨mem_UH' h fun x y => by rw [hn, hn, h.2.2.1, h.2.2.1, hm], fun a i hi => ?_, fun i j hj hj' hi => ?_⟩
  · have := coord_span h he i (S := {b | b < a}) (fun b hb => lt_of_lt_of_le (Fin.lt_def.1 hb) hi) (h2 a)
    rw [phi_sub' h, ← hn, he, mulVec_smul, ← smul_sub, Pi.smul_apply, smul_eq_zero, or_iff_right (hρ a), Pi.sub_apply,
      sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this
  · let P : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u =>
      u - ∑ a : Fin r, herm (Hpk k r) u (Φ (e a)) • Φ (f a)
    have hP : ∀ u, (n *ᵥ P u - P u) i = 0 := by
      refine span_ind' h _ (fun x => ?_) (fun u v hu hv => ?_) (fun c u hu => ?_)
      · have ex : P (Φ x) = Φ (x - ∑ a : Fin r, H.B x (e a) • f a) := by
          simp only [P, phi_sub' h, phi_sum' h, h.2.1, h.2.2.1]
        rw [ex, hn, ← phi_sub' h]
        have hperp : ∀ b, H.B (e b) (x - ∑ a : Fin r, H.B x (e a) • f a) = 0 := fun b => by
          rw [map_sub, map_sum]
          simp [hef]
          rw [starRingEnd_apply, H.herm, sub_self]
        have := h3 _ hperp
        rw [← Set.image_univ] at this
        exact coord_span h he i (fun b _ => lt_of_lt_of_le b.2 hi) this
      · have ex : P (u + v) = P u + P v := by
          simp only [P, herm_add_left, add_smul, Finset.sum_add_distrib]; abel
        rw [ex, mulVec_add, add_sub_add_comm, Pi.add_apply, hu, hv, add_zero]
      · have ex : P (c • u) = c • P u := by
          simp only [P, herm_smul_left, smul_sub, Finset.smul_sum, smul_smul]
        rw [ex, mulVec_smul, ← smul_sub, Pi.smul_apply, hu, smul_zero]
    have ex : P (bvec j) = bvec j := by
      simp only [P]
      rw [Finset.sum_eq_zero, sub_zero]
      intro a _
      have hne : esI k r a ≠ j := fun e' => by
        have := congrArg Fin.val e'
        have := a.2
        simp only [esI] at *; omega
      rw [he, herm_smul_right, herm_eI]
      simp [bvec, hne]
    have := hP (bvec j)
    rw [ex, Pi.sub_apply, sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this

end GlobalTheory.DegVol.FrameUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpace
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.MidLift

open GlobalTheory.DegVol.RealMat

variable {k r j : ℕ}

private lemma Hpk_esI_apply' (a : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) i = if i = eI k r a then 1 else 0 := by
  have ha := a.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, Hpk_esI_apply']

theorem coord_eq_zero {g : Mat k r} (hg : g ∈ UH (Hpk k r))
    (hX : ∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, a.val < j → herm (Hpk k r) u (g⁻¹ *ᵥ bvec (eI k r a)) = 0)
    (b : Fin r) (hb : b.val < j) : u (eI k r b) = 0 := by
  have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hg

  have hinj : Function.Injective (Matrix.mulVecLin g⁻¹) := by
    intro x y hxy
    have h := congrArg (fun v => g *ᵥ v) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] using h

  have hli : ∀ f : {a : Fin r // a.val < j} → Fin (2 * r + k + 1), Function.Injective f →
      LinearIndependent ℂ (fun a => bvec (f a)) := by
    intro f hf
    have h := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp f hf
    convert h using 1
    funext a
    simp [bvec, Function.comp]
  have hI1 : Function.Injective fun a : {a : Fin r // a.val < j} => eI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [eI, Fin.val_mk] at h'
    exact Subtype.ext (Fin.ext h')
  have hI2 : Function.Injective fun a : {a : Fin r // a.val < j} => esI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [esI, Fin.val_mk] at h'
    have := a.1.isLt
    have := a'.1.isLt
    exact Subtype.ext (Fin.ext (by omega))
  have hl1 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1)) := hli _ hI1
  have hl2 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hli _ hI2

  have hle : (XJ k r j).map (Matrix.mulVecLin g⁻¹) ≤ XstJ k r j := by
    unfold XJ
    rw [Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact (hX a.1 a.2).1
  have hrank : Module.finrank ℂ ((XJ k r j).map (Matrix.mulVecLin g⁻¹)) = Module.finrank ℂ (XstJ k r j) := by
    rw [← (Submodule.equivMapOfInjective _ hinj (XJ k r j)).finrank_eq]
    unfold XJ XstJ
    rw [finrank_span_eq_card hl1, finrank_span_eq_card hl2]
  have heq : (XJ k r j).map (Matrix.mulVecLin g⁻¹) = XstJ k r j :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : bvec (esI k r b) ∈ (XJ k r j).map (Matrix.mulVecLin g⁻¹) := by
    rw [heq]
    unfold XstJ
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
  have hzero : ∀ x ∈ XJ k r j, herm (Hpk k r) u (g⁻¹ *ᵥ x) = 0 := by
    intro x hx
    unfold XJ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hu a.1 a.2
    | zero => simp [herm]
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, h₁, h₂, add_zero]
    | smul c y _ h => rw [Matrix.mulVec_smul, GlobalTheory.DegVol.RealMat.herm_smul_right, h, mul_zero]
  rw [← herm_esI u b, ← hxe, Matrix.mulVecLin_apply]
  exact hzero x hx

theorem inWb_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF w hw
  unfold IsFrameOf at hF
  obtain ⟨hR, -, -, -, ⟨c, hN⟩, he, hist, -, -⟩ := hF
  unfold IsReal at hR
  obtain ⟨-, -, hiso, -⟩ := hR
  unfold IsNormal0 at hN
  obtain ⟨hgG, -, -, -, -, hX, -, -⟩ := hN
  unfold GlobalTheory.DegCnt.NF.Wn at hw
  rw [GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw

  have hBe : ∀ a : Fin r, H.B w (N.F.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F.e a.castSucc) w, hw _ h1, star_zero]
  have hBe' : ∀ a : Fin r, H.B w (N.F'.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F'.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F'.e a.castSucc) w, hw _ h1, star_zero]
  have hBist : ∀ b : Fin r, N.j ≤ b.val → H.B w (N.ist b) = 0 := by
    intro b hb
    have h1 : N.ist b ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← H.herm (N.ist b) w, hw _ h1, star_zero]
  have hρ' : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (pow_pos hρ n).ne'

  have hes : ∀ a : Fin r, Φ w (esI k r a) = 0 := by
    intro a
    have h1 := hiso w (N.F.e a.castSucc)
    rw [(he a).1, GlobalTheory.DegVol.RealMat.herm_smul_right, GlobalTheory.DegVol.RealMat.herm_eI, hBe a, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 (hρ' _))

  have hhi : ∀ b : Fin r, N.j ≤ b.val → Φ w (eI k r b) = 0 := by
    intro b hb
    have h1 := hiso w (N.ist b)
    rw [hist b hb, GlobalTheory.DegVol.RealMat.herm_smul_right, herm_esI, hBist b hb, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (star_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_pos hρ _).ne')))

  have hlo : ∀ b : Fin r, b.val < N.j → Φ w (eI k r b) = 0 := by
    have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hgG
    intro b hb
    refine coord_eq_zero (j := N.j) hgG hX (fun a _ => ?_) b hb
    have h3 : Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • (g⁻¹ *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_smul, ← (he a).2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    have h2 : g⁻¹ *ᵥ bvec (eI k r a) = (((ρ ^ (r - a.val) : ℝ) : ℂ))⁻¹ • Φ (N.F'.e a.castSucc) := by
      rw [h3, inv_smul_smul₀ (hρ' _)]
    rw [h2, GlobalTheory.DegVol.RealMat.herm_smul_right, hiso, hBe' a, map_zero, mul_zero]
  unfold inWb
  intro i hi
  rcases hi with hi | hi
  · have hb : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [← hb]
    by_cases hj : i.val < N.j
    · exact hlo ⟨i.val, hi⟩ hj
    · exact hhi ⟨i.val, hi⟩ (not_lt.1 hj)
  · have hlt : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have hb : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI, Fin.val_mk]
      have := i.isLt
      omega
    rw [← hb]
    exact hes _

end GlobalTheory.DegVol.MidLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbedding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (G : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (G : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ G := by
  first
  | exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem
  | exact _root_.GlobalTheory.DenominatorTheorem.main_theorem
  | (apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)

theorem mem_locFlag_of_smul (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) {c : 𝓞 E} (hc : c ≠ 0) {y : Fin n → E}
    (hy : c • y ∈ F b) : (P⁻¹ *ᵥ fun l => φ (y l)) ∈ locFlag φ P F b := by
  have hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc
  have e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l) := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [e, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

omit [NumberField E] in
theorem mulVec_mem_of_span (φ : E →+* ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (S : Set (Fin n → E))
    (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ S, (Q *ᵥ fun l => φ (y l)) ∈ W) {u : Fin n → ℂ}
    (hu : u ∈ Submodule.span ℂ ((fun w : Fin n → E => fun i => φ (w i)) '' S)) : Q *ᵥ u ∈ W := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem _ hx

theorem form_frame {P K M : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * K * P = M)
    (u v : Fin n → ℂ) : star (P⁻¹ *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ (K *ᵥ (P *ᵥ v)) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]

omit [NumberField E] in
theorem form_emb [StarRing E] (φ : E →+* ℂ) (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    star (fun l => φ (x l)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) = φ (star x ⬝ᵥ (J *ᵥ y)) := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]

theorem locDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  intro E _ _ _ n m J φ P ε F hφ hP hJ hF hsp
  classical
  obtain ⟨hmono, h0, hm, hd⟩ := hF
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have htop : locFlag φ P F m = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [← hinv z]
    refine mulVec_mem_of_span φ _ _ _ ?_
      (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))
    intro y _
    obtain ⟨c, hc, hy⟩ := exists_smul_mem _ hsp y
    exact mem_locFlag_of_smul φ P F m hc hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, htop⟩
  · intro a b hab
    exact Submodule.span_mono (Set.image_mono (hmono hab))
  · unfold locFlag
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have : y = 0 := by simpa using hy
    subst this
    have e : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    simp only [e, Matrix.mulVec_zero]
  · intro b hb
    unfold locFlag
    rw [hm b hb]
  · intro b hb z
    constructor
    · intro hz
      refine ⟨by rw [htop]; trivial, fun x hx => ?_⟩
      induction hz using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        induction hx using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]
        | mem a ha =>
          obtain ⟨v, hv, rfl⟩ := ha
          rw [form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]
    · rintro ⟨-, hz⟩
      rw [← hinv z]
      let f : (Fin n → E) → Module.Dual E (Fin n → E) := fun x =>
        { toFun := fun y => star x ⬝ᵥ (J *ᵥ y)
          map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
      have hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y) := fun _ _ => rfl
      refine mulVec_mem_of_span φ _ _ _ ?_
        (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)
      · intro y hy
        obtain ⟨c, hc, hcy⟩ := exists_smul_mem _ hsp y
        refine mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)
        have h1 : star x ⬝ᵥ (J *ᵥ y) = 0 := hy (f x) ⟨x, hx, rfl⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)
        rw [form_frame hP hJ] at h1
        rw [← h1]
        generalize P *ᵥ z = u
        simp only [hf, Matrix.mulVec_single_one]
        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum,
          Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]
        rw [Finset.sum_comm]
        rfl

end GlobalTheory.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPos
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem satIn_of_trace (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (h : ∀ y, y ∈ S ↔ y ∈ lamX I x ∧ y ∈ Submodule.span I.E (S : Set (Fin I.n → I.E))) :
    GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S := by
  have := GlobalTheory.StepDualityCompare.totallyComplex I

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span I.E (S : Set (Fin I.n → I.E)))
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E) := q.subtype ∘ₗ Submodule.linearProjOfIsCompl q _ hq.symm
  have hker : LinearMap.ker φ = Submodule.span I.E (S : Set (Fin I.n → I.E)) := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ q.ker_subtype]
    exact Submodule.linearProjOfIsCompl_ker _
  have hX : ∀ v, IsUnit (frm I x v).det := GlobalTheory.StepDualityCompare.frm_det I x
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat := (Formalism.HN.htImage I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x)
    (bas I) (frm I x) hX hX φ (lamX I x) hfg).1
  have hS : lamX I x ⊓ (LinearMap.ker φ).restrictScalars (𝓞 I.E) = S := by
    ext y
    rw [hker, Submodule.mem_inf, Submodule.restrictScalars_mem, h]
  rw [hS] at hsat
  exact hsat

theorem sizeQ_flag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  intro I x a j S hS i
  obtain ⟨-, hmono, -, htr, -⟩ := hS
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x (S i.castSucc) := satIn_of_trace I x _ (htr i.castSucc)
  have hle : S i.succ ≤ lamX I x := fun y hy => ((htr i.succ y).1 hy).1
  have hmn : S i.castSucc ≤ S i.succ := hmono (Fin.castSucc_le_succ i)
  have hpos := GlobalTheory.StepDualityCompare.htQ_pos I x hfg _ _ hsat hle hmn
  unfold Formalism.HN.sizeQ
  exact Real.rpow_pos_of_pos hpos _

end GlobalTheory.LeviIso
end

