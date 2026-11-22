import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Grp

section Alg

variable {k : Type} [Field k]

theorem mirProj_eq_one_of_mem {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [← hv]
  simp [unip, colMat, one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one' {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) : u ∈ MirUin k n := by
  have hb : ∀ a b : Fin n, ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = if a = b then 1 else 0 := by
    intro a b
    have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) a b) hu
    exact (this : ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _).trans (by simp [one_apply])
  have hl := (mem_Mir_iff k (u : GL (Fin (n + 1)) k)).1 u.2
  refine Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd fun a => ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.last n), ?_⟩
  apply Units.ext
  ext a b
  have hlb := congrFun hl b
  induction a using Fin.lastCases with
  | last =>
    rw [hlb]
    induction b using Fin.lastCases <;> simp [unip, colMat, one_apply, eLast, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [unip, colMat, one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [hb]
      simp [unip, colMat, one_apply, Fin.castSucc_ne_last]

theorem mirUin_normal (n : ℕ) : (MirUin k n).Normal := by
  refine ⟨fun u hu g => mem_of_mirProj_eq_one' _ ?_⟩
  rw [map_mul, map_mul, mirProj_eq_one_of_mem u hu, mul_one, map_inv, mul_inv_cancel]

theorem mirUin_comm {n : ℕ} {a b : Mir k n} (ha : a ∈ MirUin k n) (hb : b ∈ MirUin k n) : a * b = b * a := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 ha : ((a : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hb : ((b : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Subtype.ext
  show (a : GL (Fin (n + 1)) k) * (b : GL (Fin (n + 1)) k) = (b : GL (Fin (n + 1)) k) * (a : GL (Fin (n + 1)) k)
  rw [← hv, ← hw, ← map_mul, mul_comm, map_mul]

def prodSub {n : ℕ} (L₁ L₂ : Subgroup (Mir k n)) (h₁ : L₁ ≤ MirUin k n) (h₂ : L₂ ≤ MirUin k n) : Subgroup (Mir k n) where
  carrier := (L₁ : Set (Mir k n)) * (L₂ : Set (Mir k n))
  one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, L₁.mul_mem ha hc, b * d, L₂.mul_mem hb hd, ?_⟩
    show a * c * (b * d) = a * b * (c * d)
    rw [mul_assoc a c, ← mul_assoc c b, mirUin_comm (h₁ hc) (h₂ hb)]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    show a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact mirUin_comm (MirUin k n |>.inv_mem (h₁ ha)) (MirUin k n |>.inv_mem (h₂ hb))

theorem hpg_entry {i t : ℕ} (g : Mir k ((i + 1) + t + 1)) (hg : g ∈ HPG k (i + 1) (t + 1))
    (l : Fin ((i + 1) + t + 2)) (hl : i < l.val) (hl2 : l.val ≠ (i + 1) + t + 1) (c : Fin (i + 1)) :
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) l
      (Fin.castLE (by omega) c) = 0 := by
  have hp : (g : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ GlobalTheory.SmGL.parab k (ePG (i + 1) (t + 1)) := hg
  have hlt := l.isLt
  have h0 := mem_parab_iff.1 hp true false (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1)) (Fin.castSucc c : Fin (i + 1 + 1)) (by decide)
  have e1 : ePG (i + 1) (t + 1) ⟨true, (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1))⟩ = l := by
    apply Fin.ext
    simp [ePG, two]
    omega
  have e2 : ePG (i + 1) (t + 1) ⟨false, (Fin.castSucc c : Fin (i + 1 + 1))⟩ = Fin.castLE (by omega) c := by
    apply Fin.ext
    simp [ePG, two]
  rw [e1, e2] at h0
  exact h0

theorem Cl_left {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + t + 1))
    (hx : x ∈ Cl k i t) : h * x ∈ Cl k i t := by
  intro c
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : l.val ≤ i
  · have := hx ⟨l.val, by omega⟩
    have e : Fin.castLE (by omega) (⟨l.val, by omega⟩ : Fin (i + 1)) = l := Fin.ext rfl
    rw [e] at this
    rw [this, zero_mul]
  · by_cases h2 : l.val = (i + 1) + t + 1
    · have e : l = Fin.last _ := Fin.ext h2
      have hm := (mem_Mir_iff k ((h⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (h⁻¹).2
      have hc := congrFun hm (Fin.castLE (by omega) c)
      rw [e, hc]
      have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
        intro e'
        have := congrArg Fin.val e'
        simp at this
        omega
      simp [eLast, Pi.single_apply, this]
    · rw [hpg_entry _ ((HPG k (i + 1) (t + 1)).inv_mem hh) l (by omega) h2 c, mul_zero]

theorem Cl_right {i t : ℕ} (x : Mir k ((i + 1) + t + 1)) (hx : x ∈ Cl k i t) (u : Mir k ((i + 1) + t + 1))
    (hu : u ∈ MirUin k ((i + 1) + t + 1)) : x * u ∈ Cl k i t := by
  intro c
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 ((MirUin k ((i + 1) + t + 1)).inv_mem hu) :
    ((u⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ MirU k ((i + 1) + t + 1))
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hw]
  have hv : ((unip k ((i + 1) + t + 1) w : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) = 1 + colMat k _ w.toAdd := rfl
  rw [hv, add_mul, one_mul, Matrix.add_apply, hx c, zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last _
  · have hm := (mem_Mir_iff k ((x⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (x⁻¹).2
    have hc := congrFun hm (Fin.castLE (by omega) c)
    rw [hl, hc]
    have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
      intro e'
      have := congrArg Fin.val e'
      simp at this
      omega
    simp [eLast, Pi.single_apply, this]
  · simp [colMat, hl]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mirChar_ker_open (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) :
    IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
  have he : ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) =
      (fun u : MirUin k (n + 1) => GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n)) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
    have hl : GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n) = w.toAdd (Fin.last n) := by
      simp only [GlobalTheory.CompanionTheory.BZFun.lastCol, ← hw]
      exact unip_apply_castSucc_last k (n + 1) w _
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, hl,
      mirChar_eq k ψ n u w hw.symm]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage
    ((continuous_apply _).comp (GlobalTheory.CompanionTheory.BZFun.continuous_lastCol k (n + 1)))

theorem isClosed_Cl (i t : ℕ) : IsClosed (Cl k i t) := by
  have hc : Continuous fun p : Mir k ((i + 1) + t + 1) =>
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  have he : Cl k i t = ⋂ c : Fin (i + 1), {p : Mir k ((i + 1) + t + 1) |
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0} := by
    ext p
    simp [Cl]
  rw [he]
  exact isClosed_iInter fun c => isClosed_eq (hc.matrix_elem _ _) continuous_const

end Top

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  intro k _ _ _ _ ψ hψ i t
  refine ⟨mirUin_normal _, mirChar_ker_open ψ hψ _, isClosed_Cl i t, fun h hh x hx => Cl_left h hh x hx,
    fun x hx u hu => Cl_right x hx u hu, fun L₁ L₂ h₁ h₂ c₁ c₂ => ⟨prodSub L₁ L₂ h₁ h₂, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (MirUin k _).mul_mem (h₁ ha) (h₂ hb)
  · exact (c₁.mul c₂ : IsCompact ((L₁ : Set (Mir k ((i + 1) + t + 1))) * (L₂ : Set (Mir k ((i + 1) + t + 1)))))
  · intro a ha
    exact ⟨a, ha, 1, L₂.one_mem, mul_one a⟩
  · intro b hb
    exact ⟨1, L₁.one_mem, b, hb, one_mul b⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Grp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (u : GL (Fin (n + 1)) k)).mp u.2
  have hrow' : ∀ j, ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      (Pi.single (Fin.last n) (1 : k) : Fin (n + 1) → k) j := by
    intro j
    rw [hrow]
    rfl
  have hblk : ∀ i j : Fin n,
      ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    exact congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hu
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n)), ?_⟩
  apply Units.ext
  ext i j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n))))) i j = _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, hrow']
    | cast j =>
      simp [GlobalTheory.BZMir.colMat, hrow', Matrix.one_apply, Pi.single_apply, Fin.castSucc_ne_last,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last, hblk]

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOne
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.DetPG

def sumSig (a b : Type) : a ⊕ b ≃ Σ x, Two a b x where
  toFun y := match y with
    | Sum.inl i => ⟨false, i⟩
    | Sum.inr j => ⟨true, j⟩
  invFun x := match x with
    | ⟨false, i⟩ => Sum.inl i
    | ⟨true, j⟩ => Sum.inr j
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_hpg (i T : ℕ) (h : HPG k i T) :
    GeneralLinearGroup.det ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
      GeneralLinearGroup.det ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
        GeneralLinearGroup.det (pgProj k i T h).2 := by
  ext
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_det_apply]
  let φ : Fin (i + 1) ⊕ Fin T ≃ Fin (i + T + 1) := (sumSig _ _).trans (ePG i T)
  have hz : ∀ (b : Fin T) (a : Fin (i + 1)),
      (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) : Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k)
        (ePG i T ⟨true, b⟩) (ePG i T ⟨false, a⟩) = 0 := fun b a =>
    mem_parab_iff.1 h.2 true false b a (by decide)
  have hb : (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
        Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k).submatrix φ φ =
      fromBlocks (((pgProj k i T h).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)
        (Matrix.of fun a b => (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
          Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k) (φ (Sum.inl a)) (φ (Sum.inr b))) 0
        ((pgProj k i T h).2 : Matrix (Fin T) (Fin T) k) := by
    ext x y
    rcases x with a | b <;> rcases y with c | d
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) false a c).symm
    · rfl
    · exact hz b c
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) true b d).symm
  rw [← det_submatrix_equiv_self φ, hb]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem dpowM_hpg (i T : ℕ) (s : ℝ) (h : HPG k i T) :
    dpowM (i + T) s (h : Mir k (i + T)) = dpowM i s (pgProj k i T h).1 * dpow T s (pgProj k i T h).2 := by
  show detChar (Fin (i + T + 1)) (absPow k (s : ℂ)) ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
    detChar (Fin (i + 1)) (absPow k (s : ℂ)) ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
      detChar (Fin T) (absPow k (s : ℂ)) (pgProj k i T h).2
  rw [detChar_apply, detChar_apply, detChar_apply, det_hpg, map_mul]

theorem dpow_add' (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem dpow_zero' (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow, absPow_zero]

theorem dpowM_add' (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n s * dpowM n t := by
  ext g
  simp [dpowM, dpow_add']

theorem dpowM_zero' (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero']

theorem complex_units_mul_eq_one_of_mul_eq_one (A B X Y Z : ℂˣ) (h₁ : A * B = 1) (h₂ : X * Y * Z = 1) : A * X * Y * (B * Z) = 1 := by
  have : A * X * Y * (B * Z) = (A * B) * (X * Y * Z) := by ac_rfl
  rw [this, h₁, h₂, one_mul]

theorem exponents_cancel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (h : HPG k i (t + 1)) :
    ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
      (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  have e1 : dpowM (k := k) i (-1 / 2) (pgProj k i (t + 1) h).1 * dpowM i (1 / 2) (pgProj k i (t + 1) h).1 = 1 := by
    have : dpowM (k := k) i (-1 / 2 + 1 / 2) = dpowM i (-1 / 2) * dpowM i (1 / 2) := dpowM_add' _ _ _
    rw [show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpowM_zero'] at this
    rw [← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e2 : dpow (k := k) (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 = 1 := by
    have : dpow (k := k) (t + 1) (-1 / 2 + 1 + -1 / 2) = dpow (t + 1) (-1 / 2) * dpow (t + 1) 1 * dpow (t + 1) (-1 / 2) := by
      rw [dpow_add', dpow_add']
    rw [show (-1 / 2 + 1 + -1 / 2 : ℝ) = 0 by norm_num, dpow_zero'] at this
    rw [← MonoidHom.mul_apply, ← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e : dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      (dpowM i (1 / 2) (pgProj k i (t + 1) h).1 * dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2) = 1 := by
    rw [dpowM_hpg]
    exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ e1 e2
  have := congrArg (Units.val) e
  simpa only [Units.val_mul, Units.val_one] using this

end GlobalTheory.CompanionTheory.BZPhiPG.DetPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactor
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolic
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ModCompactParab

theorem deltaHalf_leviProj_eq_one_of_isCompact :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ)
      (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) →
      ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K →
        deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  intro k _ _ _ _ a b n e K hK p hp
  let χ : parab k (two e) →* ℂˣ := (deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))
  have hχ : Continuous (leviProj k (two e)) := GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k) :=
    (GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal
  let H : Subgroup (parab k (two e)) := K.subgroupOf (parab k (two e))
  have hH : IsCompact (H : Set (parab k (two e))) := hemb.isCompact_preimage hK
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H) :=
    (isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)
  haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : (χ.ker.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)
  have hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1 := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa [χ, MonoidHom.mem_ker, map_pow] using h
  have hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hpow
    simp only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h
    exact_mod_cast h
  have hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1 :=
    (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal
  ext
  rw [val_deltaHalf, hone]
  simp

end GlobalTheory.CompanionTheory.ModCompactParab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_single_nonzero_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL k) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL k) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | exact GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single <;> assumption)
end

