import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def IsBump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (c : G) (v : W) (B : cIndSpace H ρ) : Prop :=
  (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a v) ∧
    ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0

end Abs

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def sO (i t : ℕ) : Mir k (i + (t + 1)) →* Mir k ((i + 1) + t + 1) :=
  (sEmb k ((i + 1) + t)).comp (castM k (by omega : i + (t + 1) = (i + 1) + t)).toMonoidHom

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Closed

open GlobalTheory.CompanionTheory.BZPhiPhi

section LinAlg

variable {k : Type} [Field k]

theorem exists_GL_row (N m : ℕ) (r : Fin (N + 1) → k) (hr0 : ∀ l : Fin (N + 1), l.val < m → r l = 0)
    (hr : r ≠ 0) :
    ∃ A : GL (Fin (N + 1)) k, (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) (Fin.last N) = r ∧
      ∀ i l : Fin (N + 1), m ≤ i.val → l.val < m → (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) i l = 0 := by
  classical
  obtain ⟨l0, hl0⟩ : ∃ l, r l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  have hml : m ≤ l0.val := by
    by_contra h
    exact hl0 (hr0 l0 (by omega))
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) k := (1 : Matrix _ _ k).updateRow l0 r
  have hB : B.det = r l0 := by
    have h1 := Matrix.cramer_apply (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k) r l0
    rw [Matrix.cramer_one] at h1
    have h2 := Matrix.updateRow_transpose (M := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k)) (j := l0) (c := r)
    rw [Matrix.transpose_one] at h2
    show ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k).updateRow l0 r).det = r l0
    rw [h2, Matrix.det_transpose, ← h1]
    rfl
  let σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap l0 (Fin.last N)
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) k := B.submatrix σ id
  have hA : A.det ≠ 0 := by
    have : A.det = _ := Matrix.det_permute σ B
    rw [this, hB]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hl0]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, ?_, ?_⟩
  · funext l
    show B (σ (Fin.last N)) l = r l
    simp [σ, B]
  · intro i l hi hl
    show B (σ i) l = 0
    have hs : m ≤ (σ i).val := by
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · have := Fin.is_lt l
        have h3 : l0.val ≤ N := by omega
        simp only [Fin.val_last]
        omega
      · exact hml
      · exact hi
    simp only [B, Matrix.updateRow_apply]
    split_ifs
    · exact hr0 l hl
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at hs
      omega

theorem levi_val (n : ℕ) (A : GL (Fin n) k) :
    (((levi k n A : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (A : Matrix (Fin n) (Fin n) k) := rfl

theorem mirProj_val (n : ℕ) (g : Mir k n) (i l : Fin n) :
    ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc l) := rfl

theorem glEmbMat_last_cast (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (l : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc l) = 0 := by
  simp [glEmbMat]

theorem mirProj_levi_eq (n : ℕ) (A : GL (Fin n) k) : mirabolicProjection k n (levi k n A) = A := by
  ext i l
  rw [mirProj_val, levi_val]
  simp [glEmbMat]

theorem rowQ_ne_zero (n : ℕ) (p : Mir k (n + 1)) : rowQ k n p ≠ 0 := by
  intro h
  have key : vecMul (eLast k n) ((mirabolicProjection k (n + 1) p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowQ k n p := by
    rw [vecMul_eLast]
    rfl
  have h2 : eLast k n = 0 := by
    have h3 := congrArg (fun v => vecMul v ((((mirabolicProjection k (n + 1) p)⁻¹ : GL (Fin (n + 1)) k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k)) key
    simp only [h, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h3
    exact h3
  have h4 := congrFun h2 (Fin.last n)
  simp [eLast] at h4

theorem entry_of_mirProj_eq_one (n : ℕ) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (i l : Fin (n + 1))
    (hil : i ≠ l) (hl : l ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l = 0 := by
  obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  induction i using Fin.lastCases with
  | last =>
    rw [(mem_Mir_iff k _).1 u.2]
    simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  | cast i =>
    rw [← mirProj_val, hu]
    have : i ≠ l' := fun e => hil (by rw [e])
    simp [Matrix.one_apply, this]

theorem row_levi (n : ℕ) (y : Mir k n) (t : Fin (n + 2)) :
    (((levi k (n + 1) (y : GL (Fin (n + 1)) k) : Mir k (n + 1)) : GL (Fin (n + 2)) k) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t := by
  rw [levi_val]
  have hy := (mem_Mir_iff k _).1 y.2
  induction t using Fin.lastCases with
  | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
  | cast t =>
    simp only [glEmbMat, Fin.lastCases_castSucc]
    rw [hy]
    by_cases h : t = Fin.last n
    · subst h; simp [eLast]
    · have : (Fin.last n) ≠ t := fun e => h e.symm
      simp [eLast, Pi.single_apply, h, Matrix.one_apply, this]

end LinAlg

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_mirabolicParabolic_iff_lt (m j : ℕ) (g : Mir k (m + (j + 1))) :
    g ∈ MirabolicParabolic k m (j + 1) ↔ ∀ i l : Fin (m + (j + 1) + 1), m ≤ i.val → l.val < m →
      ((g : GL (Fin (m + (j + 1) + 1)) k) : Matrix (Fin (m + (j + 1) + 1)) (Fin (m + (j + 1) + 1)) k) i l = 0 := by
  rw [mem_mirabolicParabolic_iff]
  constructor
  · intro h i l hi hl
    have hb : i.val - m < j + 1 + 1 := by have := i.2; omega
    have h1 := h ⟨i.val - m, hb⟩ ⟨l.val, hl⟩
    have e1 : eGP m (j + 1) ⟨true, ⟨i.val - m, hb⟩⟩ = i := Fin.ext (by rw [blockIndex_true_val]; simp; omega)
    have e2 : eGP m (j + 1) ⟨false, ⟨l.val, hl⟩⟩ = l := Fin.ext (by rw [blockIndex_false_val])
    rwa [e1, e2] at h1
  · intro h b a
    apply h
    · rw [blockIndex_true_val]; omega
    · rw [blockIndex_false_val]; exact a.2

theorem set_eq (m j : ℕ) :
    {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} =
      {g | ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0} := by
  ext g
  constructor
  · rintro ⟨h, hh, x, rfl⟩ l hl
    have e : (h * embedding₂ k (m + j) x)⁻¹ = embedding₂ k (m + j) x⁻¹ * h⁻¹ := by
      rw [_root_.mul_inv_rev, map_inv]
    rw [e]
    have hi := (mem_mirabolicParabolic_iff_lt k m j h⁻¹).1 (inv_mem hh)
    show ((embedding₂ k (m + j) x⁻¹).1.1 * (h⁻¹ : Mir k (m + j + 1)).1.1)
        (Fin.castSucc (Fin.last (m + j))) (Fin.castSucc l) = 0
    rw [Matrix.mul_apply]
    simp only [embedding₂, MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [row_levi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hi _ _ (by simp) (by simpa using hl)
  · intro hg
    obtain ⟨A, hA1, hA2⟩ := exists_GL_row (m + j) m (rowQ k (m + j) g⁻¹) hg (rowQ_ne_zero _ _)
    let d : Mir k (m + (j + 1)) := levi k (m + j + 1) A
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      have hl' : l ≠ Fin.last (m + j + 1) := by
        intro e; rw [e] at hl; simp at hl; omega
      obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl'
      show (levi k (m + j + 1) A).1.1 i _ = 0
      rw [levi_val]
      induction i using Fin.lastCases with
      | last => exact glEmbMat_last_cast _ _ _
      | cast i =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact hA2 i l' (by simpa using hi) (by simpa using hl)
    have rd : rowQ k (m + j) d = rowQ k (m + j) g⁻¹ := by
      funext l
      have : rowQ k (m + j) d l = (A : Matrix _ _ k) (Fin.last (m + j)) l := by
        show (levi k (m + j + 1) A).1.1 _ _ = _
        rw [levi_val]
        simp [glEmbMat]
      rw [this, hA1]
    have hq : g⁻¹ * d⁻¹ ∈ Q k (m + j) := mul_inv_mem_Q_of_rowQ_eq _ _ _ rd.symm
    have hq' : (g⁻¹ * d⁻¹)⁻¹ ∈ Q k (m + j) := inv_mem hq
    let y : Mir k (m + j) := ⟨mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹, hq'⟩
    let u : Mir k (m + j + 1) := (g⁻¹ * d⁻¹)⁻¹ * (embedding₂ k (m + j) y)⁻¹
    have hu : mirabolicProjection k (m + j + 1) u = 1 := by
      simp only [u, map_mul, map_inv (mirabolicProjection k (m + j + 1)) (embedding₂ k (m + j) y)]
      have : mirabolicProjection k (m + j + 1) (embedding₂ k (m + j) y) = mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹ :=
        mirProj_levi_eq _ _
      rw [this]
      simp
    have huH : u ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      refine entry_of_mirProj_eq_one _ u hu i l ?_ ?_
      · intro e; rw [e] at hi; omega
      · intro e; rw [e] at hl; simp at hl; omega
    refine ⟨d⁻¹ * u, mul_mem (inv_mem hd) huH, y, ?_⟩
    simp only [u]
    group

theorem isClosed_HGP_iota (m j : ℕ) :
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  rw [set_eq]
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_eq (((continuous_apply l).comp (continuous_rowQ (m + j))).comp continuous_inv) continuous_const

end Conc

end GlobalTheory.CompanionTheory.LeibPhi.Closed

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

def fibM (X Z : Type) [TopologicalSpace X] [AddCommGroup Z] [Module ℂ Z] : Submodule ℂ (X → Z) where
  carrier := {φ | IsLocallyConstant φ ∧ HasCompactSupport φ}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c φ hφ := ⟨hφ.1.comp (fun z => c • z), hφ.2.comp_left (g := fun z => c • z) (smul_zero c)⟩

section Cols

variable {k : Type}

def topP (i t : ℕ) (y : Fin (i + t) → k) : Fin i → k := fun j => y (Fin.castAdd t j)

def middlePart (i t : ℕ) (y : Fin (i + t) → k) : Fin t → k := fun j => y (Fin.natAdd i j)

theorem middlePart_add [Add k] (i t : ℕ) (a b : Fin (i + t) → k) : middlePart i t (a + b) = middlePart i t a + middlePart i t b := rfl

theorem continuous_topP [TopologicalSpace k] (i t : ℕ) : Continuous (topP (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_midP [TopologicalSpace k] (i t : ℕ) : Continuous (middlePart (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

end Cols

section Act

variable {k Z : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [AddCommGroup Z] [Module ℂ Z]

def fibAct {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) :
    Representation ℂ (Multiplicative (Fin (i + t) → k)) (fibM (Fin t → k) Z) where
  toFun y :=
    { toFun := fun φ => ⟨fun v => ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)), by
        have hh : Continuous fun v : Fin t → k => v + middlePart i t y.toAdd := continuous_id.add continuous_const
        have hl : IsLocallyConstant fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) := φ.2.1.comp_continuous hh
        have hc : HasCompactSupport fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) :=
          φ.2.2.comp_homeomorph (Homeomorph.addRight (middlePart i t y.toAdd))
        exact ⟨hl.comp _, hc.comp_left (map_zero _)⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext v
        exact map_add _ _ _
      map_smul' := fun c a => by
        apply Subtype.ext
        funext v
        exact map_smul _ _ _ }
  map_one' := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t 0)) (φ.1 (v + middlePart i t 0)) = φ.1 v
    have h1 : Multiplicative.ofAdd (topP (k := k) i t 0) = 1 := rfl
    have h2 : middlePart (k := k) i t 0 = 0 := rfl
    rw [h1, h2, map_one, add_zero]
    rfl
  map_mul' a b := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd))) (φ.1 (v + middlePart i t (a.toAdd + b.toAdd))) =
      ρ₀ (Multiplicative.ofAdd (topP i t a.toAdd)) (ρ₀ (Multiplicative.ofAdd (topP i t b.toAdd)) (φ.1 (v + middlePart i t a.toAdd + middlePart i t b.toAdd)))
    have h1 : Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd)) =
        Multiplicative.ofAdd (topP i t a.toAdd) * Multiplicative.ofAdd (topP i t b.toAdd) := rfl
    rw [h1, map_mul, middlePart_add, add_assoc]
    rfl

theorem fibAct_apply {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    (y : Multiplicative (Fin (i + t) → k)) (φ : fibM (Fin t → k) Z) (v : Fin t → k) :
    (fibAct t ρ₀ y φ).1 v = ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) := rfl

end Act

section Field

variable {k : Type} [Field k]

def uMh (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n where
  toFun y := uM k n y.toAdd
  map_one' := uM_zero k n
  map_mul' a b := uM_add k n a.toAdd b.toAdd

def mulH {n : ℕ} (κ : GL (Fin n) k) : Multiplicative (Fin n → k) →* Multiplicative (Fin n → k) where
  toFun y := Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec y.toAdd)
  map_one' := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec (a.toAdd + b.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

def topRep {i : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k i) V)
    (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (Multiplicative (Fin i → k)) (V ⊗[ℂ] W) where
  toFun x := LinearMap.rTensor W (τ (uM k i x.toAdd))
  map_one' := by
    show LinearMap.rTensor W (τ (uM k i 0)) = 1
    rw [uM_zero, map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    show LinearMap.rTensor W (τ (uM k i (a.toAdd + b.toAdd))) = _
    rw [uM_add, map_mul]
    exact LinearMap.rTensor_mul _ _ _

end Field

section Lat

variable {k : Type} [Field k] [ValuativeRel k]

def Lc (n : ℕ) (c : k) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {y | ∀ j, c * y.toAdd j ∈ 𝒪[k]}
  mul_mem' := by
    intro a b ha hb j
    have : c * (a * b).toAdd j = c * a.toAdd j + c * b.toAdd j := mul_add _ _ _
    rw [this]
    exact add_mem (ha j) (hb j)
  one_mem' := by
    intro j
    have : c * (1 : Multiplicative (Fin n → k)).toAdd j = 0 := mul_zero _
    rw [this]
    exact zero_mem _
  inv_mem' := by
    intro a ha j
    have : c * (a⁻¹).toAdd j = - (c * a.toAdd j) := by
      show c * (- a.toAdd j) = _
      ring
    rw [this]
    exact neg_mem (ha j)

theorem mem_Lc {n : ℕ} {c : k} {y : Multiplicative (Fin n → k)} : y ∈ Lc n c ↔ ∀ j, c * y.toAdd j ∈ 𝒪[k] := Iff.rfl

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_Lc (n : ℕ) (c : k) : IsOpen (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hset : (Lc n c : Set (Multiplicative (Fin n → k))) =
      ⋂ j, (fun y : Multiplicative (Fin n → k) => c * y.toAdd j) ⁻¹' (𝒪[k] : Set k) := by
    ext y
    simp only [SetLike.mem_coe, mem_Lc, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  have hO : IsOpen (𝒪[k] : Set k) := by exact Valuation.isOpen_integer
  exact isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_const.mul ((continuous_apply j).comp continuous_toAdd))

theorem isCompact_Lc (n : ℕ) {c : k} (hc : c ≠ 0) : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hf : Continuous fun x : Fin n → k => Multiplicative.ofAdd (c⁻¹ • x) :=
    continuous_ofAdd.comp (continuous_const_smul _)
  convert hK.image hf using 1
  ext y
  constructor
  · intro hy
    refine ⟨c • y.toAdd, fun j _ => ?_, ?_⟩
    · have h := mem_Lc.1 hy j
      rw [Valuation.mem_integer_iff] at h
      simpa using h
    · simp [smul_smul, hc]
  · rintro ⟨x, hx, rfl⟩
    refine mem_Lc.2 fun j => ?_
    rw [Valuation.mem_integer_iff]
    simpa [smul_smul, hc] using hx j trivial

end Lat

section Coset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def cosetSet (t : ℕ) (c : k) (a : Fin t → k) : Set (Fin t → k) :=
  {v | Multiplicative.ofAdd (v - a) ∈ Lc t c}

theorem isClopen_cosetSet (t : ℕ) (c : k) (a : Fin t → k) : IsClopen (cosetSet t c a) := by
  have hcont : Continuous fun v : Fin t → k => Multiplicative.ofAdd (v - a) :=
    continuous_ofAdd.comp (continuous_id.sub continuous_const)
  have h1 : IsOpen (Lc t c : Set (Multiplicative (Fin t → k))) := isOpen_Lc t c
  exact ⟨(Subgroup.isClosed_of_isOpen _ h1).preimage hcont, h1.preimage hcont⟩

theorem isCompact_cosetSet (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) : IsCompact (cosetSet t c a) := by
  have h := (isCompact_Lc t hc).image (f := fun y : Multiplicative (Fin t → k) => y.toAdd + a)
    ((continuous_toAdd).add continuous_const)
  convert h using 1
  ext v
  constructor
  · intro hv
    exact ⟨Multiplicative.ofAdd (v - a), hv, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show Multiplicative.ofAdd (y.toAdd + a - a) ∈ Lc t c
    simpa using hy

def cosetFn (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) : fibM (Fin t → k) Z :=
  ⟨(cosetSet t c a).indicator fun _ => z, by
      classical
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ cosetSet t c a
      · exact ⟨_, (isClopen_cosetSet t c a).2, hx, fun y hy => by
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
      · exact ⟨_, (isClopen_cosetSet t c a).1.isOpen_compl, hx, fun y hy => by
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩,
    by
      haveI : T2Space k := inferInstance
      exact HasCompactSupport.intro (isCompact_cosetSet t hc a) fun x hx => Set.indicator_of_notMem hx _⟩

end Coset

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem exists_Qp_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  intro k _ _ _ _ i t g
  obtain ⟨u, l, w, hw, hg⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : i + t = i + t))) g
  refine ⟨⟨(u : GL (Fin (i + t)) k) * GlobalTheory.SmGL.leviEmb k _ l, ?_⟩, w, hw, hg⟩
  exact Subgroup.mul_mem _ (GlobalTheory.SmGL.unipRad_le_parab k _ u.2)
    (GlobalTheory.SmGL.leviEmb_mem_parab k _ l)

end GlobalTheory.CompanionTheory.BZPsiPG
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjectiveStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_projection_fixed_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd) := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac | exact GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac | (intros; apply GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac <;> assumption)
end

