import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0453

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

def sh (x : Tl l) : ℂ_[l] := ((PreTilt.untilt x : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l])

def omC : Om l →+* ℂ_[l] := algebraMap (Om l) ℂ_[l]

theorem omC_apply (y : Om l) : omC y = (y : ℂ_[l]) := (PadicComplex.coe_eq _ y).symm

theorem norm_omC (y : Om l) : ‖omC y‖ = ‖y‖ := by
  rw [omC_apply, PadicComplex.norm_extends]

def oc (K : FinExt l) : ↥(OL K) →+* ℂ_[l] :=
  (omC (l := l)).comp ((K.1.val : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

theorem oc_apply (K : FinExt l) (c : ↥(OL K)) : oc K c = (((c : ↥K.1) : Om l) : ℂ_[l]) :=
  omC_apply _

theorem norm_oc_le_one (K : FinExt l) (c : ↥(OL K)) : ‖oc K c‖ ≤ 1 := by
  have h := (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K (c : ↥K.1)).1 (GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K c).2
  rw [oc_apply, PadicComplex.norm_extends]
  exact h

@[simp] theorem sh_zero : sh (0 : Tl l) = 0 := by
  simp [sh, GroundTheory.PAdicHodge.untilt_zero]

@[simp] theorem sh_one : sh (1 : Tl l) = 1 := by
  simp [sh]

theorem sh_mul (x y : Tl l) : sh (x * y) = sh x * sh y := by
  simp [sh, GroundTheory.PAdicHodge.untilt_mul]

theorem sh_pow (x : Tl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, sh_mul, ih]

theorem norm_eq_norm_sh (x : Tl l) : ‖x‖ = ‖sh x‖ := rfl

theorem norm_sh_le_one (x : Tl l) : ‖sh x‖ ≤ 1 := GroundTheory.PAdicHodge.norm_untilt_le_one x

theorem sh_eq_zero {x : Tl l} : sh x = 0 ↔ x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff

theorem norm_sh_add_sub_le (x y : Tl l) : ‖sh (x + y) - (sh x + sh y)‖ ≤ ‖(l : ℂ_[l])‖ := by
  simpa [sh] using GroundTheory.PAdicHodge.norm_untilt_add_sub_le x y

theorem exists_sh_near (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) : ∃ x : Tl l, ‖sh x - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨x, hx⟩ := GroundTheory.PAdicHodge.exists_mk_untilt_eq (K := ℂ_[l]) (p := l)
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  exact ⟨x, by simpa [sh] using (GroundTheory.PAdicHodge.mk_eq_mk_iff_norm_sub_le (p := l)).1 hx⟩

theorem thB_tch (x : Tl l) : thB l (tch l x) = sh x := by
  show GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l (wB l (WittVector.teichmuller l x)) = _
  rw [wB, GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus,
    WittVector.fontaineTheta_teichmuller]
  rfl

theorem thB_rB (y : Om l) : thB l (rB l y) = (y : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l y

theorem tch_mul (x y : Tl l) : tch l (x * y) = tch l x * tch l y := by
  simp [tch, map_mul]

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  induction n with
  | zero => simp [tch]
  | succ n ih => rw [pow_succ, pow_succ, tch_mul, ih]

theorem sh_actT (g : GQ l) (x : Tl l) :
    sh (actT g x) = GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (sh x) :=
  GroundTheory.PAdicHodge.AInf.coe_untilt_gal (Formalism.Per6.toBot g) x

theorem galCp_omC (g : GQ l) (y : Om l) :
    GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (omC y) = omC (g y) := by
  rw [omC_apply, omC_apply]
  exact GroundTheory.PAdicHodge.galCp_coe (Formalism.Per6.toBot g) y

theorem norm_galCp (g : GQ l) (x : ℂ_[l]) : ‖GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) x‖ = ‖x‖ :=
  GroundTheory.PAdicHodge.norm_galCp _ x

theorem norm_sub_pow (x y : Tl l) (f : ℕ) : ‖x ^ l ^ f - y ^ l ^ f‖ = ‖x - y‖ ^ l ^ f := by
  rw [← sub_pow_char_pow, norm_pow]

section Near

variable {ρ : ℝ}

theorem near_add (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x + y) - (A + B)‖ ≤ ρ := by
  have e : sh (x + y) - (A + B) = (sh (x + y) - (sh x + sh y)) + ((sh x - A) + (sh y - B)) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((norm_sh_add_sub_le x y).trans hρ)
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)))

theorem near_mul {x y : Tl l} {A B : ℂ_[l]} (hB : ‖B‖ ≤ 1) (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x * y) - A * B‖ ≤ ρ := by
  have e : sh (x * y) - A * B = sh x * (sh y - B) + (sh x - A) * B := by rw [sh_mul]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sh_le_one x)).trans hy
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hB).trans hx

theorem near_neg (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ) :
    ‖sh (-x) - (-A)‖ ≤ ρ := by
  have h := norm_sh_add_sub_le x (-x)
  rw [add_neg_cancel, sh_zero, zero_sub, norm_neg] at h
  have e : sh (-x) - (-A) = (sh x + sh (-x)) - (sh x - A) := by ring
  rw [e, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (h.trans hρ) (by rw [norm_neg]; exact hx))

theorem near_sub (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x - y) - (A - B)‖ ≤ ρ := by
  rw [sub_eq_add_neg x y, sub_eq_add_neg A B]
  exact near_add hρ hx (near_neg hρ hy)

theorem near_pow (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hA : ‖A‖ ≤ 1)
    (hx : ‖sh x - A‖ ≤ ρ) (n : ℕ) : ‖sh (x ^ n) - A ^ n‖ ≤ ρ := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hρ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact near_mul hA ih hx

theorem near_sum (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {ι : Type*} (s : Finset ι) {x : ι → Tl l}
    {A : ι → ℂ_[l]} (hx : ∀ i ∈ s, ‖sh (x i) - A i‖ ≤ ρ) :
    ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, A i‖ ≤ ρ := by
  induction s using Finset.induction_on with
  | empty => simpa using (norm_nonneg _).trans hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact near_add hρ (hx a (Finset.mem_insert_self _ _))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem near_of_norm_sub_le (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖x - y‖ ≤ ρ) :
    ‖sh x - sh y‖ ≤ ρ := by
  have h1 : ‖sh (x - y) - 0‖ ≤ ρ := by rw [sub_zero]; exact h
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  simpa using near_add hρ h1 h2

theorem norm_sub_le_of_near (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖sh x - sh y‖ ≤ ρ) :
    ‖x - y‖ ≤ ρ := by
  have h1 : ‖sh x - sh x‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h3 := near_sub hρ h1 h2
  have e : sh (x - y) = (sh (x - y) - (sh x - sh y)) + (sh x - sh y) := by ring
  rw [norm_eq_norm_sh, e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h)

end Near

theorem fixed_unique {f : ℕ} (hf : 0 < f) {x y : Tl l} (hx : x ^ l ^ f = x) (hy : y ^ l ^ f = y)
    (h : ‖x - y‖ < 1) : x = y := by
  have h1 : ‖x - y‖ = ‖x - y‖ ^ l ^ f := by rw [← norm_sub_pow, hx, hy]
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have := pow_lt_self_of_lt_one₀ hpos h hq
  linarith

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniqueness
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Stab

section Perm

theorem piPerm_true_val (i t : ℕ) (x : Fin (t + 1)) (hx : i + x.val < (i + 1) + t + 1) :
    (piPerm i t ⟨i + x.val, hx⟩).val = i + 1 + x.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨i + x.val, hx⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨true, x⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val]

theorem piPerm_false_val (i t : ℕ) (y : Fin i) (hy : y.val < (i + 1) + t + 1) :
    (piPerm i t ⟨y.val, hy⟩).val = y.val := by
  have h : (finCongr (by omega : i + 1 + t + 1 = i + (t + 1) + 1) ⟨y.val, hy⟩ :
      Fin (i + (t + 1) + 1)) = GlobalTheory.BZMir.Leib.ePG i (t + 1) ⟨false, Fin.castSucc y⟩ :=
    Fin.ext (by simp [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val])
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]
  rw [h, Equiv.symm_apply_apply, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val]
  all_goals simp

end Perm

section Ent

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_symm_entry {a b : ℕ} (e : a = b) (r : Mir k b) (x y : ℕ) (hx : x < a + 1) (hy : y < a + 1)
    (hx' : x < b + 1) (hy' : y < b + 1) :
    (((castM k e).symm r : Mir k a) : GL (Fin (a + 1)) k).val ⟨x, hx⟩ ⟨y, hy⟩ =
      (r : GL (Fin (b + 1)) k).val ⟨x, hx'⟩ ⟨y, hy'⟩ := by
  subst e
  rfl

theorem mirProj_dEmb (i t : ℕ) (d : Fin (t + 1) → k) : mirabolicProjection k _ (dEmb k i t d) = 1 := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirProj_eq_one_of_mem
  exact Subgroup.mem_subgroupOf.mpr
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem mirProj_wEl (i t : ℕ) : mirabolicProjection k _ (wEl k i t) = wGL k i t :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem mirProj_sEmb (n : ℕ) (r : Mir k n) : mirabolicProjection k _ (sEmb k n r) = (r : GL (Fin (n + 1)) k) :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

theorem wGL_mul_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    ((wGL k i t).val * M) (piPerm i t a) b = M a b := by
  show (Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹ * M) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t a) b = M a b
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  simp

theorem mul_wGL_apply (i t : ℕ) (M : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (a b : Fin ((i + 1) + t + 1)) :
    (M * (wGL k i t).val) a b = M a (piPerm i t b) := by
  show (M * Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t)⁻¹) a b = M a (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t b)
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  simp [Equiv.Perm.inv_def]

theorem entry_eq (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y =
      (h : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc (piPerm i t x)) (Fin.castSucc (piPerm i t y)) := by
  have key := congrArg (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t + 1)) e
  simp only [map_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_dEmb, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_wEl,
    GlobalTheory.CompanionTheory.BZPhiPG.Stab.mirProj_sEmb, _root_.one_mul, _root_.mul_one] at key
  have key' := congrArg (fun g : GL (Fin ((i + 1) + t + 1)) k =>
    (g : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x) y) key
  simp only [Units.val_mul, GlobalTheory.CompanionTheory.BZPhiPG.Stab.wGL_mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.Stab.mul_wGL_apply] at key'
  exact key'

theorem entry_zero (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k) (h : Mir k ((i + 1) + t + 1))
    (hh : h ∈ HPG k (i + 1) (t + 1))
    (e : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t)
    (x y : Fin ((i + 1) + t + 1)) (hx : i < (piPerm i t x).val) (hy : (piPerm i t y).val ≤ i) :
    (r : GL (Fin ((i + 1) + t + 1)) k).val x y = 0 := by
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_eq i t r d d' h e x y]
  have hc : (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ) < i + 1 := by omega
  have hz := GlobalTheory.CompanionTheory.BZPhiPG.Grp.hpg_entry h hh
    (Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x))
    (by rw [Fin.coe_castSucc]; exact hx)
    (by rw [Fin.coe_castSucc]; exact Nat.ne_of_lt (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t x).isLt)
    ⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩
  have e₂ : (Fin.castLE (by omega) (⟨(GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y : ℕ), hc⟩ : Fin (i + 1)) :
      Fin ((i + 1) + t + 1 + 1)) = Fin.castSucc (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t y) := Fin.ext rfl
  rw [e₂] at hz
  exact hz

end Ent

theorem mem_of_double_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  intro k _ _ _ _ i t r d d' h hh e
  have hab : i + (t + 1) = (i + 1) + t := by omega
  refine ⟨(GlobalTheory.CompanionTheory.BZPhiPG.castM k hab).symm r, ?_, MulEquiv.apply_symm_apply _ _⟩
  apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.mem_HPG_of
  · intro x y
    have hxl := x.isLt
    have hyl := y.isLt
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) y.val (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_false_val]; omega)
  · intro x
    have hxl := x.isLt
    have hcol : (Fin.last (i + (t + 1)) : Fin (i + (t + 1) + 1)) = ⟨(i + 1) + t, by omega⟩ :=
      Fin.ext (by rw [Fin.val_last, Fin.val_mk]; omega)
    rw [hcol]
    refine (GlobalTheory.CompanionTheory.BZPhiPG.Stab.castM_symm_entry hab r (i + x.val) ((i + 1) + t) (by omega) (by omega)
      (by omega) (by omega)).trans ?_
    exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.entry_zero i t r d d' h hh e _ _
      (by rw [GlobalTheory.CompanionTheory.BZPhiPG.Stab.piPerm_true_val]; omega) (GlobalTheory.CompanionTheory.BZPhiPG.Cells.piPerm_last_val i t).le

end GlobalTheory.CompanionTheory.BZPhiPG.Stab

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompatStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_unipotent_character_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | exact GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdInj

theorem prod₂_map_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (f : σ.IntertwiningMap σ'), Function.Injective f → ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ), Function.Injective F := by
  intro k _ _ _ _ r t U U' W _ _ _ _ _ _ σ σ' ρ f hf
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.ProdInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwinerStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_map_induced_surjective_intertwiner : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → IsSmooth σ → Function.Surjective q →
    (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ F : cIndSpace H' σ', ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq <;> assumption)
end

