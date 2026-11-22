import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolume
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCell
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wPerm_last {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e, ePG_false_last]

theorem vecMul_wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k))
      (wGL k h : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
  ext c
  rw [Matrix.single_one_vecMul]
  show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _
  rw [wPerm_last]
  simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem vecMul_wGL_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k) := by
  rw [← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem mem_parab_of_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k)
    (y : Fin (i + t + 1) → k)
    (hg : (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix _ _ k).updateRow (stdSum h (Sum.inl (Fin.last i))) y) :
    g ∈ parab k (two (stdSum h)) := by
  rw [mem_parab_iff]
  intro a b x z hab
  have hab' : a = true ∧ b = false := by
    clear x z
    revert hab
    cases a <;> cases b <;> decide
  obtain ⟨rfl, rfl⟩ := hab'
  have hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i)) := by
    intro e
    have := (stdSum h).injective e
    simp at this
  have hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩ := by
    intro e
    have := (two (stdSum h)).injective e
    simp at this
  rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]

theorem locSec_wGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1) : LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  intro OQ hOQ OP hOP
  set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁
  set w := wGL k h with hw
  obtain ⟨b, hbc, hb1, hb⟩ := exists_rowSec (k := k) a₁
  let y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k := fun u =>
    vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
  have hyc : Continuous y :=
    continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)
  have hy1 : y 1 = Pi.single a₁ 1 := by
    simp only [y, mul_one]
    exact vecMul_wGL_inv h
  have hBc : ContinuousAt (fun u => b (y u)) 1 :=
    ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt
  have hB1 : b (y 1) = 1 := by rw [hy1, hb1]
  have hS : ContinuousAt (fun u => (b (y u))⁻¹) 1 := hBc.inv
  have hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1 :=
    ((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id
  have hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ :=
    hS.eventually_mem (by simpa [hB1] using hOQ)
  have hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP :=
    hP.eventually_mem (by simpa [hB1] using hOP)
  have hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0 := by
    have : ContinuousAt (fun u => y u a₁) 1 := ((continuous_apply a₁).comp hyc).continuousAt
    exact this.eventually_ne (by rw [hy1]; simp)
  refine ⟨_, hS'.and (hP'.and hne), ?_⟩
  rintro u ⟨h1, h2, h3⟩ -
  have hBm := hb (y u) h3
  refine ⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩
  show vecMul (eLast k (i + t)) _ = eLast k (i + t)
  have e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))
      (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u := by
    rw [vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]
    exact Matrix.updateRow_self
  have e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
    simp only [y]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
        (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
          ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKGL
section
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo.JIwaAd

section Dg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dg_mem_stab (s : Set (ι ⊕ ι)) (x : Rˣ) : dg ι x ∈ stab R s := by
  intro r hr c hc
  have hne : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne⟩

theorem det_dg {i : ι} (hi : ∀ y, y = i) (x : Rˣ) : Matrix.GeneralLinearGroup.det (dg ι x) = x := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal _).det = _
  rw [Matrix.det_diagonal, Fintype.prod_sum_type]
  simp

theorem map_dg {S : Type} [CommRing S] (f : R →+* S) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (dg ι x) = dg ι (Units.map f.toMonoidHom x) := by
  apply Units.ext
  show (Matrix.diagonal _).map f = Matrix.diagonal _
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext a
  cases a <;> simp

theorem dg_mul (x y : Rˣ) : dg ι (x * y) = dg ι x * dg ι y := by
  apply Units.ext
  show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  cases a <;> simp

end Dg

section Ad

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R)

theorem dg_mem_kGL {ι : Type} [Fintype ι] [DecidableEq ι] (x : Rˣ) (h1 : (x : R) ∈ A.O)
    (h2 : ((x⁻¹ : Rˣ) : R) ∈ A.O) (h3 : ∀ w, ‖A.φ w x‖ = 1) : dg ι x ∈ A.kGL (ι ⊕ ι) := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h1, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h2, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show (Matrix.diagonal _).map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ
    rw [Matrix.diagonal_map (map_zero _), Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases a with
    | inl a => simp
    | inr a =>
      simp only [Function.comp, Sum.elim_inr, Pi.star_apply, RCLike.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, h3 w]
      simp

variable {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_O {M : Matrix n n R} (h : ∀ r c, M r c ∈ A.O) : M.det ∈ A.O := by
  rw [Matrix.det_apply']
  exact A.O.sum_mem fun s _ => A.O.mul_mem (intCast_mem _ _) (A.O.prod_mem fun m _ => h _ _)

theorem det_kGL {k : GL n R} (hk : k ∈ A.kGL n) :
    ((Matrix.GeneralLinearGroup.det k : Rˣ) : R) ∈ A.O ∧
      (((Matrix.GeneralLinearGroup.det k)⁻¹ : Rˣ) : R) ∈ A.O ∧
      ∀ w, ‖A.φ w (Matrix.GeneralLinearGroup.det k : Rˣ)‖ = 1 := by
  refine ⟨?_, ?_, fun w => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).1
  · rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).2
  · have h := Matrix.det_of_mem_unitary (hk.2 w)
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have h' : star (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det * (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det = 1 :=
      Unitary.star_mul_self_of_mem h
    have h2 : ‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ ^ 2 = 1 := by
      have := congrArg norm h'
      simpa [sq] using this
    nlinarith [norm_nonneg (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det, sq_nonneg (‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ - 1)]

end Ad

section Main

open GroundTheory.Global

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R]

theorem map_mem_kGL {A : Ad E R} {ε : ℤˣ} {ν : 𝔸[F] →+* R} {r : R → 𝔸[F]} {δ : Eˣ} {α : IdeleGroup F}
    {ω : HeckeCharacter F} (hB : Base A ε ν r δ α ω) {n : Type} [Fintype n] [DecidableEq n]
    {k : GL n 𝔸[F]} (hk : k ∈ (adStd F).kGL n) : Matrix.GeneralLinearGroup.map ν k ∈ A.kGL n := by
  refine ⟨fun a b => ⟨(hB.int _).2 (hk.1 a b).1, ?_⟩, fun w => ?_⟩
  · rw [← map_inv]
    exact (hB.int _).2 (hk.1 a b).2
  · obtain ⟨v, hv⟩ := hB.inf w
    have e : ((Matrix.GeneralLinearGroup.map ν k : GL n R) : Matrix n n R).map (A.φ w) =
        (k : Matrix n n 𝔸[F]).map ((adStd F).φ v) := by
      ext a b
      simp [hv]
    rw [e]
    exact hk.2 v

theorem jiwa : StdGood → JIwa := by
  intro hS F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hB hi hJ x
  obtain ⟨b, hb, κ, hκ, hbk⟩ := (hS F).iwa (ι ⊕ ι) {Sum.inl i} ((dg ι α)⁻¹ * x.1.2 * dg ι α)
  obtain ⟨c1, c2, c3⟩ := det_kGL (adStd F) hκ
  set c := Matrix.GeneralLinearGroup.det κ with hc
  have ht : dg ι c ∈ (adStd F).kGL (ι ⊕ ι) := dg_mem_kGL _ c c1 c2 c3
  set κ' : GL (ι ⊕ ι) 𝔸[F] := (dg ι c)⁻¹ * κ with hκ'
  have hκ'K : κ' ∈ (adStd F).kGL (ι ⊕ ι) := mul_mem (inv_mem ht) hκ
  have hdet : Matrix.GeneralLinearGroup.det κ' = 1 := by
    rw [hκ', map_mul, map_inv, det_dg hi, ← hc, inv_mul_cancel]
  set d : GL (ι ⊕ ι) 𝔸[F] := dg ι α with hd
  have hdet2 : Matrix.GeneralLinearGroup.det (d * κ' * d⁻¹) = 1 := by
    simp [map_mul, hdet, mul_comm]
  have hkc : ((1 : Rˣ), d * κ' * d⁻¹) ∈ cover A ν ι := by
    simp [cover, MonoidHom.mem_ker, hdet2]
  let k : cover A ν ι := ⟨_, hkc⟩
  have hjk : (j k).1 ∈ A.kGL (ι ⊕ ι) := by
    obtain ⟨u, hu, u1, u2, u3⟩ := hB.δα
    have hδ : Units.map A.i.toMonoidHom δ = Units.map ν.toMonoidHom α * u := Units.ext hu
    have e : (j k).1 = (dg ι (Units.map A.i.toMonoidHom δ))⁻¹ * Matrix.GeneralLinearGroup.map ν k.1.2 *
        dg ι (Units.map A.i.toMonoidHom δ) := by
      apply Units.ext
      rw [hJ k]
      show ((1 : Rˣ) : R) • _ = _
      rw [Units.val_one, one_smul]
    have e2 : (j k).1 = (dg ι u)⁻¹ * Matrix.GeneralLinearGroup.map ν κ' * dg ι u := by
      have hD : dg ι (Units.map ν.toMonoidHom α) = Matrix.GeneralLinearGroup.map ν d := (map_dg ν α).symm
      have hk2 : Matrix.GeneralLinearGroup.map ν k.1.2 = Matrix.GeneralLinearGroup.map ν d *
          Matrix.GeneralLinearGroup.map ν κ' * (Matrix.GeneralLinearGroup.map ν d)⁻¹ := by
        show Matrix.GeneralLinearGroup.map ν (d * κ' * d⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [e, hδ, dg_mul, hD, hk2]
      generalize Matrix.GeneralLinearGroup.map ν d = P
      generalize Matrix.GeneralLinearGroup.map ν κ' = Q
      generalize dg ι u = T
      group
    rw [e2]
    have hU : dg ι u ∈ A.kGL (ι ⊕ ι) := dg_mem_kGL A u u1 u2 u3
    exact mul_mem (mul_mem (inv_mem hU) (map_mem_kGL hB hκ'K)) hU
  have hkK : k ∈ cK α j := by
    refine ⟨hjk, ?_⟩
    exact ⟨κ', hκ'K, rfl⟩
  refine ⟨x * k⁻¹, ?_, k, hkK, by simp⟩
  have hx : x.1.2 = d * (b * κ) * d⁻¹ := by
    rw [← hbk]
    group
  have hp : prj A ν ι (x * k⁻¹) = d * (b * dg ι c) * d⁻¹ := by
    rw [map_mul, map_inv]
    show x.1.2 * (d * κ' * d⁻¹)⁻¹ = _
    rw [hx, hκ']
    group
  show prj A ν ι (x * k⁻¹) ∈ stab 𝔸[F] {Sum.inl i}
  rw [hp]
  have hdS : d ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := dg_mem_stab _ _
  exact mul_mem (mul_mem hdS (mul_mem hb (dg_mem_stab _ _))) (inv_mem hdS)

end Main

end GlobalTheory.CompanionTheory.RgEisSo.JIwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabLine
section
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisJ

section Ring

variable {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_entry (d : Sˣ) (g : GL (ι ⊕ ι) S) (r c : ι ⊕ ι) :
    (((dg ι d)⁻¹ * g * dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c =
      Sum.elim (fun _ => (1 : S)) (fun _ => ((d⁻¹ : Sˣ) : S)) r * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c *
        Sum.elim (fun _ => (1 : S)) (fun _ => (d : S)) c := by
  have h1 : (((dg ι d)⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => ((d⁻¹ : Sˣ) : S)) := rfl
  have h2 : ((dg ι d : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) =
      Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => (d : S)) := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_stab_line {i : ι} (hi : ∀ x, x = i) (s : Set (ι ⊕ ι)) (hs : s = {Sum.inl i}) (g : GL (ι ⊕ ι) S) :
    g ∈ stab S s ↔ (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (Sum.inr i) (Sum.inl i) = 0 := by
  subst hs
  have e : g ∈ stab S ({Sum.inl i} : Set (ι ⊕ ι)) ↔ ∀ r ∉ ({Sum.inl i} : Set (ι ⊕ ι)), ∀ c ∈ ({Sum.inl i} : Set (ι ⊕ ι)),
      (g : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 ∧ ((g⁻¹ : GL (ι ⊕ ι) S) : Matrix (ι ⊕ ι) (ι ⊕ ι) S) r c = 0 := Iff.rfl
  rw [e]
  constructor
  · intro h
    exact h _ (by simp) _ rfl
  · rintro h r hr c hc
    obtain rfl : c = Sum.inl i := hc
    rcases r with y | y
    · exact absurd (by rw [hi y]; rfl) hr
    · rw [hi y]; exact h

theorem det_tri {i : ι} (hi : ∀ x, x = i) (h : Matrix (ι ⊕ ι) (ι ⊕ ι) S) (h0 : h (Sum.inr i) (Sum.inl i) = 0) :
    h.det = h (Sum.inl i) (Sum.inl i) * h (Sum.inr i) (Sum.inr i) := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  have e : h = Matrix.fromBlocks h.toBlocks₁₁ h.toBlocks₁₂ 0 h.toBlocks₂₂ := by
    ext r c
    rcases r with y | y <;> rcases c with z | z
    · rfl
    · rfl
    · rw [hi y, hi z]; simpa using h0
    · rfl
  rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]
  have hd : (default : ι) = i := hi _
  simp [hd, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem bdet_val {κ : Type} [Fintype κ] [DecidableEq κ] (s : Set κ) (c : κ) (hs : s = {c}) (g : GL κ S)
    (hu : IsUnit ((g : Matrix κ κ S) c c)) : ((bdet s g : Sˣ) : S) = (g : Matrix κ κ S) c c := by
  subst hs
  have e : ∀ (f : Fintype ↥({c} : Set κ)) (dq : DecidableEq ↥({c} : Set κ)),
      @Matrix.det _ dq f S _ ((g : Matrix κ κ S).submatrix (Subtype.val : ({c} : Set κ) → κ) Subtype.val) =
        (g : Matrix κ κ S) c c := by
    intro f dq
    exact Matrix.det_eq_elem_of_subsingleton _ (⟨c, rfl⟩ : ({c} : Set κ))
  unfold bdet
  split_ifs with h
  · exact h.unit_spec.trans (e _ _)
  · exact absurd (by rw [e]; exact hu) h

end Ring

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]
  {A : Ad E R} {ν : 𝔸[F] →+* R} {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ℤˣ}

theorem j_entry {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (x : cover A ν ι) (r c : ι ⊕ ι) :
    (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) r c = (x.1.1 : R) *
      (Sum.elim (fun _ => (1 : R)) (fun _ => (((Units.map A.i.toMonoidHom δ)⁻¹ : Rˣ) : R)) r *
        ν ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) r c) *
        Sum.elim (fun _ => (1 : R)) (fun _ => ((Units.map A.i.toMonoidHom δ : Rˣ) : R)) c) := by
  rw [hJ x, Matrix.smul_apply, smul_eq_mul, conj_entry]
  rfl

theorem j_low {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) (x : cover A ν ι)
    (i : ι) : (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl i) = 0 ↔
      (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inl i) = 0 := by
  rw [j_entry hJ x, Sum.elim_inr, Sum.elim_inl, mul_one, Units.mul_right_eq_zero, Units.mul_right_eq_zero,
    map_eq_zero_iff ν hν]

theorem image_univ {i : ι} (hi : ∀ x, x = i) : (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  constructor
  · rintro ⟨z, -, rfl⟩
    rw [hi z]; rfl
  · intro h
    obtain rfl : y = Sum.inl i := h
    exact ⟨i, trivial, rfl⟩

theorem compl_inr {i : ι} (hi : ∀ x, x = i) : ({Sum.inr i}ᶜ : Set (ι ⊕ ι)) = {Sum.inl i} := by
  ext y
  rcases y with y | y
  · rw [hi y]; simp
  · rw [hi y]; simp

theorem comap_uQ {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) (hν : Function.Injective ν) {i : ι}
    (hi : ∀ x, x = i) :
    (A.uQ ε Set.univ).comap j = (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) := by
  ext x
  have e1 : x ∈ (A.uQ ε Set.univ).comap j ↔ (j x).1 ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := Iff.rfl
  have e2 : x ∈ (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) ↔ x.1.2 ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := Iff.rfl
  have e3 : ((j x).1)⁻¹ = (j x⁻¹).1 := by rw [map_inv]; rfl
  have e4 : (x.1.2)⁻¹ = (x⁻¹).1.2 := rfl
  rw [e1, e2, mem_stab_line hi _ (image_univ hi), mem_stab_line hi _ rfl, e3, e4, j_low hJ hν, j_low hJ hν]

theorem blocks {δ : Eˣ} {j : cover A ν ι →* A.U ε ι} (hJ : IsJ δ j) {i : ι} (hi : ∀ x, x = i) (x : cover A ν ι)
    (hx : prj A ν ι x ∈ stab 𝔸[F] {Sum.inl i}) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (j x).1 = x.1.1 * Units.map ν.toMonoidHom (bdet {Sum.inl i} (prj A ν ι x)) ∧
    Matrix.GeneralLinearGroup.det (prj A ν ι x) = bdet {Sum.inl i} (prj A ν ι x) * bdet {Sum.inr i} (prj A ν ι x) := by
  have hp : ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) = x.1.2 := rfl
  have h0 := ((mem_stab_line hi _ rfl _).1 hx).1
  have hdet := det_tri hi _ h0
  have hu : IsUnit (((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inl i) (Sum.inl i) *
      ((prj A ν ι x : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) (Sum.inr i) (Sum.inr i)) := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (prj A ν ι x).isUnit
  have h1 := isUnit_of_mul_isUnit_left hu
  have h2 := isUnit_of_mul_isUnit_right hu
  have b1 := bdet_val _ _ rfl _ h1
  have b2 := bdet_val _ _ rfl _ h2
  have he := j_entry hJ x (Sum.inl i) (Sum.inl i)
  rw [Sum.elim_inl, Sum.elim_inl, one_mul, mul_one] at he
  have hju : IsUnit ((((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)) := by
    rw [he]
    exact x.1.1.isUnit.mul (h1.map ν)
  refine ⟨Units.ext ?_, Units.ext ?_⟩
  · rw [bdet_val _ (Sum.inl i) (image_univ hi) _ hju, he, Units.val_mul]
    congr 1
    exact (congrArg ν b1).symm
  · rw [Units.val_mul, b1, b2, ← hdet]
    rfl

theorem jPar : JPar := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j _ hB hi hJ
  exact ⟨by rw [compl_inr hi], comap_uQ hJ hB.inj hi, fun x hx => blocks hJ hi x hx⟩

end GlobalTheory.CompanionTheory.EisJ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.MirClosed

theorem isClosed_mirabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
      IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  intro k _ _ _ _ n
  haveI : T2Space k := GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField (k := k)
  have e : (Mir k n : Set (GL (Fin (n + 1)) k)) =
      ⋂ j : Fin (n + 1), {g : GL (Fin (n + 1)) k |
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = eLast k n j} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rw [mem_Mir_iff k g]
    exact funext_iff
  rw [e]
  have hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val
  refine isClosed_iInter fun j => ?_
  exact isClosed_eq ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval))
    continuous_const

end GlobalTheory.CompanionTheory.BZRes.MirClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolumeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_integral_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.radical_integral | exact GlobalTheory.CompanionTheory.Rodier.radical_integral | (intros; apply GlobalTheory.CompanionTheory.Rodier.radical_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecompositionStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_eigenvalue_pair_decomposition : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | exact GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | (intros; apply GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join <;> assumption)
end

