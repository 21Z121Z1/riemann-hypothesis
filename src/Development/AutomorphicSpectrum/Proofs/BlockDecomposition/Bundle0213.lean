import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eventuallyEq_of_agree_GLs {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) {x : Mat n}
    (hx : x ∈ GLs n) : F =ᶠ[nhds x] F' := by
  have ho : IsOpen (GLs n) := by
    have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne.preimage this
  exact Filter.eventuallyEq_of_mem (ho.mem_nhds hx) h

theorem Rd_agree_GLs (X : Mat n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Rd X F x = Rd X F' x := by
  intro x hx
  simp only [Rd, (eventuallyEq_of_agree_GLs h hx).fderiv_eq]

theorem Eu_agree_GLs (s : Bool) (a b : Fin n) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, Eu s a b F x = Eu s a b F' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_agree_GLs _ h x hx]

theorem Epow_agree_GLs (s : Bool) (m : ℕ) (a b : Fin n) {F F' : Mat n → V}
    (h : ∀ g ∈ GLs n, F g = F' g) : ∀ x ∈ GLs n, Epow s m a b F x = Epow s m a b F' x := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    by_cases hab : a = b
    · simpa [Epow, hab] using h x hx
    · simp [Epow, hab]
  | succ m ih =>
    intro x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_agree_GLs s a c (ih c b) x hx

theorem gel_agree_GLs (s : Bool) (m : ℕ) {F F' : Mat n → V} (h : ∀ g ∈ GLs n, F g = F' g) :
    ∀ x ∈ GLs n, gel s m F x = gel s m F' x := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => Epow_agree_GLs s m a a h x hx

end Local

theorem zOp_agree_GLs : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) (F F' : Mat n → V), (∀ g ∈ GLs n, F g = F' g) →
    ∀ x ∈ GLs n, zOp w F x = zOp w F' x := by
  intro n V _ _ w
  induction w with
  | nil => exact fun F F' h x hx => h x hx
  | cons p w ih => exact fun F F' h => gel_agree_GLs p.1 p.2 (ih F F' h)

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.OmDec

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_sub_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g)
    (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f - h) g v = fderiv ℝ f g v - fderiv ℝ h g v := by
  rw [fderiv_sub hf hh]; rfl

theorem fderiv_zero_apply' (g v : E) : fderiv ℝ (0 : E → F) g v = 0 := by
  have h : fderiv ℝ (0 : E → F) g = 0 := by
    simpa using (fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : F))
  rw [h]; rfl

end General

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_left (A B : Mat n) (h : Mat n → V) : Rd (A - B) h = Rd A h - Rd B h := by
  funext g; simp [Rd, mul_sub]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  exact fderiv_zero_apply' _ _

theorem Rd_add_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a + b) g = Rd X a g + Rd X b g :=
  RCalc.fderiv_add_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_sub_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a - b) g = Rd X a g - Rd X b g :=
  fderiv_sub_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_smul_right (c : ℂ) (X : Mat n) {a : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • a) g = c • Rd X a g :=
  RCalc.fderiv_csmul_apply (RCalc.differentiableAt_of_smooth ha hg) c _

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  show ∑ d, Eu s c d (Epow s 0 d a f) = _
  rw [Finset.sum_eq_single a]
  · simp [Epow]
  · intro d _ hd
    simp [Epow, hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) :
    gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show ∑ c, Eu s a c (Epow s 1 c a f) = _
  simp only [Epow_one]

theorem Eu_Eu_apply (s : Bool) (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) (ε : ℂ)
    (hε : ε = if s then -Complex.I else Complex.I) :
    Eu s a b (Eu s c d f) g = (1 / 4 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        + ε • Rd (Matrix.single a b 1) (Rd (Matrix.single c d Complex.I) f) g
        + ε • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d 1) f) g
        + (ε * ε) • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  have hX := RCalc.Rd_contDiffOn (Matrix.single c d (1 : ℂ)) hf
  have hY := RCalc.Rd_contDiffOn (Matrix.single c d Complex.I) hf
  have hS : ContDiffOn ℝ ∞ (ε • Rd (Matrix.single c d Complex.I) f) (GLs n) := hY.const_smul ε
  have key : ∀ Z : Mat n, Rd Z (Eu s c d f) g =
      (1 / 2 : ℂ) • (Rd Z (Rd (Matrix.single c d 1) f) g
        + ε • Rd Z (Rd (Matrix.single c d Complex.I) f) g) := by
    intro Z
    have e : Eu s c d f = (1 / 2 : ℂ) • (Rd (Matrix.single c d 1) f
        + ε • Rd (Matrix.single c d Complex.I) f) := by
      rw [hε]; rfl
    have hA : ContDiffOn ℝ ∞ (Rd (Matrix.single c d 1) f + ε • Rd (Matrix.single c d Complex.I) f)
        (GLs n) := hX.add hS
    rw [e, Rd_smul_right _ _ hA hg, Rd_add_right _ hX hS hg, Rd_smul_right _ _ hY hg]
  have e2 : Eu s a b (Eu s c d f) g = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) (Eu s c d f) g
      + ε • Rd (Matrix.single a b Complex.I) (Eu s c d f) g) := by
    rw [hε]; rfl
  rw [e2, key, key]
  module

theorem Eu_pair_apply (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu true a b (Eu true c d f) g + Eu false a b (Eu false c d f) g = (1 / 2 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  rw [Eu_Eu_apply true a b c d hf hg (-Complex.I) (by simp),
    Eu_Eu_apply false a b c d hf hg Complex.I (by simp)]
  have h1 : (-Complex.I) * (-Complex.I) = -1 := by simp
  have h2 : Complex.I * Complex.I = -1 := by simp
  rw [h1, h2]
  module

theorem Om_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om f g = ∑ a, ∑ b, (Rd (Matrix.single a b 1) (Rd (Matrix.single b a 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single b a Complex.I) f) g) := by
  have h : Om f g = (2 : ℂ) • ∑ a, ∑ b,
      (Eu true a b (Eu true b a f) g + Eu false a b (Eu false b a f) g) := by
    simp only [Om, gel_two, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib]
  rw [h]
  simp only [Eu_pair_apply _ _ _ _ hf hg, Finset.smul_sum, smul_smul]
  norm_num

theorem Rd_sq_add (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A + B) (Rd (A + B) f) g =
      Rd A (Rd A f) g + Rd A (Rd B f) g + Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [RCalc.Rd_add_left A B f, RCalc.Rd_add_left A B (Rd A f + Rd B f)]
  simp only [Pi.add_apply]
  rw [Rd_add_right _ dA dB hg, Rd_add_right _ dA dB hg]
  abel

theorem Rd_sq_sub (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A - B) (Rd (A - B) f) g =
      Rd A (Rd A f) g - Rd A (Rd B f) g - Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [Rd_sub_left A B f, Rd_sub_left A B (Rd A f - Rd B f)]
  simp only [Pi.sub_apply]
  rw [Rd_sub_right _ dA dB hg, Rd_sub_right _ dA dB hg]
  abel

theorem sum_Ix (F : Ix n → V) :
    ∑ p, F p = ∑ a, ∑ b, (F (true, a, b) + F (false, a, b)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

theorem sum_reindex (x y : Fin n → Fin n → V) :
    ∑ a, ∑ b, (x a b - y a b) = (1 / 4 : ℂ) • ∑ a, ∑ b,
      ((2 : ℂ) • (x a b + x b a) - (2 : ℂ) • (y a b + y b a)) := by
  have hx : ∑ a, ∑ b, x b a = ∑ a, ∑ b, x a b := Finset.sum_comm
  have hy : ∑ a, ∑ b, y b a = ∑ a, ∑ b, y a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hx, hy]
  module

theorem Om_eq_squares {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) :
    ContDiffOn ℝ ∞ f (GLs n) → ∀ g ∈ GLs n,
      Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g
        - (1 / 4 : ℂ) • ∑ p : Ix n, Rd (sk p) (Rd (sk p) f) g := by
  intro hf g hg
  rw [Om_apply hf hg, sum_reindex, sum_Ix, sum_Ix, ← smul_sub]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : hm (n := n) (true, a, b) = Matrix.single a b 1 + Matrix.single b a 1 := by simp [hm]
  have e2 : hm (n := n) (false, a, b) =
      Matrix.single a b Complex.I - Matrix.single b a Complex.I := by simp [hm]
  have e3 : sk (n := n) (true, a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by simp [sk]
  have e4 : sk (n := n) (false, a, b) =
      Matrix.single a b Complex.I + Matrix.single b a Complex.I := by simp [sk]
  rw [e1, e2, e3, e4, Rd_sq_add _ _ hf hg, Rd_sq_sub _ _ hf hg, Rd_sq_add _ _ hf hg,
    Rd_sq_sub _ _ hf hg]
  module

end GlobalTheory.CompanionTheory.WaveSpd.OmDec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
section
open Matrix

namespace GlobalTheory.CompanionTheory.Flag

theorem exists_frame_extension {n D : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (h1 : Cᴴ * C = 1)
    (U : Submodule ℂ (Fin n → ℂ)) (hU : ∀ v, C *ᵥ v ∈ U) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ Cᴴ * B = 0 ∧
      ∀ y, y ∈ U ↔ ∃ u w, y = C *ᵥ u + B *ᵥ w := by
  classical
  let W' : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (Matrix.mulVecLin Cᴴ)
  obtain ⟨r, B, hB1, hBW⟩ := GlobalTheory.IsoTorus.exists_frame W'
  have hmemW' : ∀ y, y ∈ W' ↔ y ∈ U ∧ Cᴴ *ᵥ y = 0 := fun y => by
    simp [W', Submodule.mem_inf]
  have hBin : ∀ w, B *ᵥ w ∈ W' := fun w => (hBW _).mpr (by
    rw [Matrix.mulVec_mulVec w (B * Bᴴ) B, Matrix.mul_assoc, hB1, Matrix.mul_one])
  have hCB : Cᴴ * B = 0 := by
    ext i j
    have h := congrFun ((hmemW' _).mp (hBin (Pi.single j 1))).2 i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  refine ⟨r, B, hB1, hCB, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨z, hzdef⟩ : ∃ z, z = y - C *ᵥ (Cᴴ *ᵥ y) := ⟨_, rfl⟩
    have hCC : Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ y)) = Cᴴ *ᵥ y := by
      rw [Matrix.mulVec_mulVec (Cᴴ *ᵥ y) Cᴴ C, h1, Matrix.one_mulVec]
    have hz : z ∈ W' := (hmemW' z).mpr ⟨hzdef ▸ U.sub_mem hy (hU _), by
      rw [hzdef, Matrix.mulVec_sub, hCC, sub_self]⟩
    have hz' := (hBW z).mp hz
    refine ⟨Cᴴ *ᵥ y, Bᴴ *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec z B Bᴴ, hz', hzdef]
    abel
  · rintro ⟨u, w, rfl⟩
    exact U.add_mem (hU u) ((hmemW' _).mp (hBin w)).1

private theorem append_cols_mulVec_eq_add {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (v : Fin (D + r) → ℂ) :
    (Matrix.of fun i => Fin.append (C i) (B i)) *ᵥ v =
      C *ᵥ (fun j => v (Fin.castAdd r j)) + B *ᵥ (fun j => v (Fin.natAdd D j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

private theorem append_cols_conjTranspose_mul_eq_one {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (h1 : Cᴴ * C = 1) (h2 : Bᴴ * B = 1) (h3 : Cᴴ * B = 0) :
    (Matrix.of fun i => Fin.append (C i) (B i))ᴴ * (Matrix.of fun i => Fin.append (C i) (B i)) = 1 := by
  have h4 : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose h3
  ext c c'
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> refine Fin.addCases (fun j' => ?_) (fun j' => ?_) c'
  · have h := congrFun (congrFun h1 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have hne : Fin.castAdd r j ≠ Fin.natAdd D j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h3 j) j'
    simpa [Matrix.mul_apply] using h
  · have hne : Fin.natAdd D j ≠ Fin.castAdd r j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h4 j) j'
    simpa [Matrix.mul_apply] using h
  · have h := congrFun (congrFun h2 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem exists_flag_frame : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧
      Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  intro n a
  induction a with
  | zero =>
    intro W hW0 _
    refine ⟨0, 0, fun _ => 0, ?_, fun x _ _ => x.elim0, fun c => c.elim0, fun i y => ?_⟩
    · ext i j
      exact i.elim0
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      rw [hW0, Submodule.mem_bot]
      constructor
      · rintro rfl
        exact ⟨0, by simp, fun c => c.elim0⟩
      · rintro ⟨v, rfl, -⟩
        simp
  | succ a ih =>
    intro W hW0 hWm
    obtain ⟨D, C, τ, hC1, hτm, hτa, hCW⟩ := ih (fun i => W i.castSucc) (by simpa using hW0)
      (fun i j hij => hWm (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hU : ∀ v, C *ᵥ v ∈ W (Fin.last (a + 1)) := fun v =>
      hWm (Fin.castSucc_lt_last (Fin.last a)).le
        ((hCW (Fin.last a) _).mpr ⟨v, rfl, fun c h => absurd h (not_le.mpr (hτa c))⟩)
    obtain ⟨r, B, hB1, hCB, hBU⟩ := exists_frame_extension C hC1 (W (Fin.last (a + 1))) hU
    refine ⟨D + r, Matrix.of fun i => Fin.append (C i) (B i), Fin.append τ (fun _ => a),
      append_cols_conjTranspose_mul_eq_one C B hC1 hB1 hCB, ?_, ?_, ?_⟩
    · intro c c' hcc'
      induction c using Fin.addCases with
      | left j =>
        induction c' using Fin.addCases with
        | left j' =>
          simp only [Fin.append_left]
          exact hτm (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hcc'))
        | right j' =>
          simp only [Fin.append_left, Fin.append_right]
          exact (hτa j).le
      | right j =>
        induction c' using Fin.addCases with
        | left j' =>
          exfalso
          have h := Fin.le_iff_val_le_val.mp hcc'
          have := j'.isLt
          simp at h
          omega
        | right j' =>
          simp only [Fin.append_right]
          exact le_refl _
    · intro c
      refine Fin.addCases (fun j => ?_) (fun j => ?_) c
      · simp only [Fin.append_left]
        exact (hτa j).trans (Nat.lt_succ_self a)
      · simp only [Fin.append_right]
        exact Nat.lt_succ_self a
    · intro i y
      induction i using Fin.lastCases with
      | last =>
        rw [hBU]
        constructor
        · rintro ⟨u, w, rfl⟩
          refine ⟨Fin.append u w, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp
          · exfalso
            revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro h
              simp only [Fin.append_left, Fin.val_last] at h
              have := hτa j
              omega
            · intro h
              simp only [Fin.append_right, Fin.val_last] at h
              omega
        · rintro ⟨v, rfl, -⟩
          exact ⟨_, _, append_cols_mulVec_eq_add C B v⟩
      | cast i' =>
        refine (hCW i' y).trans ?_
        constructor
        · rintro ⟨v, rfl, hv⟩
          refine ⟨Fin.append v 0, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
            rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, add_zero]
          · revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro hc
              simp only [Fin.append_left, Fin.val_castSucc] at hc ⊢
              exact hv j hc
            · intro _
              simp
        · rintro ⟨v, rfl, hv⟩
          refine ⟨fun j => v (Fin.castAdd r j), ?_, fun c hc => hv (Fin.castAdd r c) (by simpa using hc)⟩
          rw [append_cols_mulVec_eq_add]
          have hz : (fun j => v (Fin.natAdd D j)) = 0 := funext fun j => hv _ (by
            have := i'.isLt
            simp only [Fin.append_right, Fin.val_castSucc]
            omega)
          rw [hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Flag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralDoubleSum
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Sym

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_add Rd_smul differentiableAt_of_smooth Rd_contDiffOn isOpen_GLs)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Expand

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Expand

section Pairing

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrable_of_cpt (hL : LgFacts) {F : Mat n → ℂ} (hc : ContinuousOn F (GLs n)) (hF : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hF
  have hc' : Continuous fun y : G n => F y.val :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  refine hc'.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem cpt_inner_left {u v : Mat n → V} (hu : Cpt u) : Cpt fun y => ⟪u y, v y⟫_ℂ := by
  obtain ⟨R, hR⟩ := hu
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem integrable_inner (hL : LgFacts) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n))
    (hv : ContDiffOn ℝ ∞ v (GLs n)) (hc : Cpt fun y => ⟪u y, v y⟫_ℂ) :
    Integrable (fun y : G n => ⟪u y.val, v y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (F := fun y => ⟪u y, v y⟫_ℂ) (hu.inner ℂ hv).continuousOn hc

end Pairing

end GlobalTheory.CompanionTheory.WaveK.Sym
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRepUnique
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.RepUnique

theorem isRep_unique : ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b b' : Mat n → V) (y : Lp V 2 μ), ContinuousOn b (GLs n) → ContinuousOn b' (GLs n) → IsRep μ b y → IsRep μ b' y → ∀ x ∈ GLs n, b x = b' x := by
  intro n _ _ μ _ V _ _ b b' y hb hb' h h' x hx
  have hv : ∀ g : G n, g.val ∈ GLs n := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have c1 : Continuous fun g : G n => b g.val := hb.comp_continuous Units.continuous_val hv
  have c2 : Continuous fun g : G n => b' g.val := hb'.comp_continuous Units.continuous_val hv
  have e : (fun g : G n => b g.val) =ᵐ[μ] fun g => b' g.val := h.symm.trans h'
  have hfun := (Continuous.ae_eq_iff_eq μ c1 c2).1 e
  exact congrFun hfun (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx)

end GlobalTheory.CompanionTheory.WaveCp.RepUnique
end
end

