import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryUnitriangularizingFlagStabilizer
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagTorus

theorem witt_partners {E V : Type} [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e : Fin r → V) (he : LinearIndependent E e)
    (hee : ∀ a b, h (e a) (e b) = 0) :
    ∃ f : Fin r → V, (∀ a b, h (e a) (f b) = if a = b then 1 else 0) ∧ ∀ a b, h (f a) (f b) = 0 := by
  classical
  let Φ : V →ₗ[E] (Fin r → E) := LinearMap.pi (fun a => h (e a))
  have hΦ : ∀ y a, Φ y a = h (e a) y := fun y a => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    apply hφ0
    have hvan : ∀ y, ∑ a, φ (Pi.single a 1) * h (e a) y = 0 := by
      intro y
      have hcomp : φ ∘ₗ Φ = 0 := by
        rw [← LinearMap.range_eq_bot, LinearMap.range_comp, hφ]
      have h0 : φ (Φ y) = 0 := LinearMap.congr_fun hcomp y
      rw [← h0]
      conv_rhs => rw [pi_eq_sum_univ (Φ y)]
      simp only [map_sum, map_smul, smul_eq_mul, hΦ, mul_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 2; ext j; simp [Pi.single_apply, eq_comm]
    have hz : ∑ a, star (φ (Pi.single a 1)) • e a = 0 := hnd _ (fun y => by
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, star_star]
      exact hvan y)
    have hc := Fintype.linearIndependent_iff.1 he _ hz
    ext a
    have := hc a
    simpa using this
  choose g hg using fun b : Fin r => hsurj (Pi.single b 1)
  have hge : ∀ a b, h (e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hΦ, hg b, Pi.single_apply]
  have hg'e : ∀ a b, h (g a) (e b) = if b = a then 1 else 0 := by
    intro a b; rw [← hsymm, hge b a]; split_ifs <;> simp
  refine ⟨fun b => g b - ∑ c, (h (g c) (g b) / 2) • e c, ?_, ?_⟩
  · intro a b
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, sub_zero, hge]
  · intro a b
    simp only [map_sub, map_sum, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hee, hge, hg'e, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply]
    have hM : star (h (g b) (g a)) = h (g a) (g b) := hsymm _ _
    have h2 : star (2 : E) = 2 := by simp
    rw [star_div₀, hM, h2]
    have : (2 : E) ≠ 0 := two_ne_zero
    field_simp
    ring

theorem diag_isometry {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e f : Fin r → V)
    (hee : ∀ a b, h (e a) (e b) = 0) (hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0)
    (hff : ∀ a b, h (f a) (f b) = 0) (α : Fin r → E) (hα : ∀ a, α a ≠ 0) :
    ∃ t : V ≃ₗ[E] V, (∀ x y, h (t x) (t y) = h x y) ∧ (∀ a, t (e a) = α a • e a) ∧
      ∀ x, (∀ a, h (e a) x = 0) → t x - x ∈ Submodule.span E (Set.range e) := by
  classical
  set β : Fin r → E := fun a => (star (α a))⁻¹ with hβ
  have hβ1 : ∀ a, star (β a) * α a = 1 := by
    intro a; simp only [hβ, star_inv₀, star_star]; exact inv_mul_cancel₀ (hα a)
  have hβ2 : ∀ a, star (α a) * β a = 1 := by
    intro a; simp only [hβ]; exact mul_inv_cancel₀ (star_ne_zero.2 (hα a))
  have hfe : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b; rw [← hsymm, hef b a]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  let L : V →ₗ[E] V := LinearMap.id + ∑ a, (α a - 1) • (h (f a)).smulRight (e a) +
    ∑ a, (β a - 1) • (h (e a)).smulRight (f a)
  have hL : ∀ x, L x = x + ∑ a, ((α a - 1) * h (f a) x) • e a + ∑ a, ((β a - 1) * h (e a) x) • f a := by
    intro x; simp [L, LinearMap.sum_apply, mul_smul]
  have key_e : ∀ b y, h (e b) (L y) = β b * h (e b) y := by
    intro b y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hee, hef, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_f : ∀ b y, h (f b) (L y) = α b * h (f b) y := by
    intro b y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hff, hfe, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_x : ∀ x y, h x (L y) = h x y + ∑ a, ((α a - 1) * h (f a) y) * star (h (e a) x) +
      ∑ a, ((β a - 1) * h (e a) y) * star (h (f a) x) := by
    intro x y
    rw [hL]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hsymm]
  have hiso : ∀ x y, h (L x) (L y) = h x y := by
    intro x y
    rw [hL x]
    simp only [map_add, LinearMap.add_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, key_e, key_f, key_x, RingHom.id_apply, starRingEnd_apply]
    have : ∀ a, ((α a - 1) * h (f a) y) * star (h (e a) x) + ((β a - 1) * h (e a) y) * star (h (f a) x) +
        star ((α a - 1) * h (f a) x) * (β a * h (e a) y) + star ((β a - 1) * h (e a) x) * (α a * h (f a) y) = 0 := by
      intro a
      simp only [star_mul', star_sub, star_one]
      linear_combination (star (h (e a) x) * h (f a) y) * hβ1 a + (star (h (f a) x) * h (e a) y) * hβ2 a
    have hsum := Finset.sum_eq_zero (s := Finset.univ) (fun a _ => this a)
    simp only [Finset.sum_add_distrib] at hsum
    linear_combination hsum
  have hinj : Function.Injective L := by
    intro x y hxy
    have : x - y = 0 := hnd _ (fun z => by
      rw [← hiso, map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply])
    exact sub_eq_zero.1 this
  refine ⟨LinearEquiv.ofInjectiveEndo L hinj, ?_, ?_, ?_⟩
  · intro x y; simpa using hiso x y
  · intro a
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hfe, hee, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      ite_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_smul, one_smul]; abel
  · intro x hx
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hx, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem flag_torus (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (γ : GV D) (hγ : γ ∈ stabF D F0) :
    ∃ t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, (∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X) ∧
      Adapt (t * γ) (lf D F0) (lf D F0) := by
  obtain ⟨hγi, hγX, hγz⟩ := hγ
  have hsymm : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hnd : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨f, hef, hff⟩ := witt_partners (VS D).hT hsymm hnd F0.e F0.e_indep F0.e_iso

  have hXa_succ : ∀ i : Fin D.R.rS, F0.Xa ((i : ℕ) + 1) = F0.Xa i ⊔ Submodule.span D.host.E {F0.e i} := by
    intro i
    have : {j : Fin D.R.rS | (j : ℕ) < (i : ℕ) + 1} = {j : Fin D.R.rS | (j : ℕ) < i} ∪ ({i} : Set (Fin D.R.rS)) := by
      ext j; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hj; rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      · rintro (h | rfl) <;> omega
    simp only [FlagG.Xa, this, Set.image_union, Set.image_singleton, Submodule.span_union]
  have hXa_top : F0.Xa D.R.rS = F0.X := by
    have : {j : Fin D.R.rS | (j : ℕ) < D.R.rS} = Set.univ := by ext j; simp [j.2]
    simp only [FlagG.Xa, FlagG.X, this, Set.image_univ]
  have he_mem : ∀ i : Fin D.R.rS, F0.e i ∈ F0.Xa ((i : ℕ) + 1) := fun i =>
    Submodule.subset_span ⟨i, by simp, rfl⟩
  have he_not : ∀ i : Fin D.R.rS, F0.e i ∉ F0.Xa i := fun i =>
    F0.e_indep.notMem_span_image (s := {j | (j : ℕ) < i}) (x := i) (by simp)
  have hdiag : ∀ i : Fin D.R.rS, ∃ u : D.host.E, u ≠ 0 ∧ γ (F0.e i) - u • F0.e i ∈ F0.Xa i := by
    intro i
    have h1 : γ (F0.e i) ∈ F0.Xa ((i : ℕ) + 1) := by
      rw [← hγX ((i : ℕ) + 1)]; exact Submodule.mem_map_of_mem (he_mem i)
    rw [hXa_succ i, Submodule.mem_sup] at h1
    obtain ⟨y, hy, w, hw, hyw⟩ := h1
    obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hw
    refine ⟨u, ?_, ?_⟩
    · rintro rfl
      apply he_not i
      have : γ (F0.e i) ∈ (F0.Xa i).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [hγX i, ← hyw]; simpa using hy
      obtain ⟨w', hw', hw'e⟩ := Submodule.mem_map.1 this
      have : w' = F0.e i := γ.injective hw'e
      exact this ▸ hw'
    · rw [← hyw]; simpa using hy
  choose u hu0 hu using hdiag
  obtain ⟨t, ht_iso, ht_e, ht_perp⟩ := diag_isometry (VS D).hT hsymm hnd F0.e f F0.e_iso hef hff
    (fun i => (u i)⁻¹) (fun i => inv_ne_zero (hu0 i))
  have ht_mem : t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun x y => ht_iso x y
  have ht_Xa : ∀ (j : ℕ), ∀ y ∈ F0.Xa j, t y ∈ F0.Xa j := by
    intro j y hy
    have : F0.Xa j ≤ (F0.Xa j).comap (t : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ht_e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    exact this hy
  have hperp : ∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X := by
    intro x hx
    exact ht_perp x (fun a => hx (F0.e a) (Submodule.subset_span ⟨a, rfl⟩))
  refine ⟨t, ht_mem, hperp, Subgroup.mul_mem _ ht_mem hγi, ?_⟩
  intro a
  induction a using Fin.lastCases with
  | last =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_last, Fin.val_last, LinearEquiv.mul_apply, hγz, Xflag]
    rw [hXa_top]
    exact hperp _ (fun x hx => by
      have := Submodule.span_le (p := LinearMap.ker ((VS D).hT.flip F0.z)) |>.2 (by
        rintro _ ⟨a, rfl⟩; simpa using F0.z_orth a) hx
      simpa using this)
  | cast i =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc, LinearEquiv.mul_apply, Xflag]
    have : γ (F0.e i) = (γ (F0.e i) - u i • F0.e i) + u i • F0.e i := by abel
    rw [this, map_add, map_smul, ht_e, smul_smul, mul_inv_cancel₀ (hu0 i), one_smul, add_sub_cancel_right]
    exact ht_Xa _ _ (hu i)

end GlobalTheory.FlagTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolume
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie

open GlobalTheory.OmegaFrobenius (realify unrealify_realify)

theorem norm_sq_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem skew_top {k : ℕ} (X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) (i j : Fin k) :
    conj (unrealify (X : EuclideanSpace ℝ _) j i) + unrealify (X : EuclideanSpace ℝ _) i j = 0 := by
  have h := (GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive k 1 (X : EuclideanSpace ℝ _) (by simp)).1 X.2
  have h' := congrFun (congrFun h i) j
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using h'

theorem lie_entry {k : ℕ} (η : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Mᴴ * Hd k η + Hd k η * M) i j =
      conj (M j i) * (if j = Fin.last k then (η : ℂ) else 1) + (if i = Fin.last k then (η : ℂ) else 1) * M i j := by
  simp [Hd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem Hd_mul_self_eq_one {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  unfold Hd
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> rcases hη with rfl | rfl <;> norm_num

theorem tang_mem {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    realify (k + 1) (tang η v) ∈ lieE (UH (Hd k η)) := by
  rw [GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (Hd_mul_self_eq_one hη), GlobalTheory.OmegaFrobenius.unrealify_realify]
  have hs := skew_top v.1
  ext i j
  rw [lie_entry, Matrix.zero_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, hs] <;> ring

theorem unrealify_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem tang_add {k : ℕ} (η : ℝ) (v w : Par k) : tang η (v + w) = tang η v + tang η w := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_add, add_div] <;> ring

theorem tang_smul {k : ℕ} (η c : ℝ) (v : Par k) : tang η (c • v) = c • tang η v := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_smul, Complex.real_smul] <;> ring

def tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Par k →ₗ[ℝ] lieE (UH (Hd k η)) where
  toFun v := ⟨realify (k + 1) (tang η v), tang_mem hη v⟩
  map_add' v w := by ext1; simp [tang_add]
  map_smul' c v := by ext1; simp [tang_smul]

theorem unrealify_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    unrealify (tangL hη v : EuclideanSpace ℝ _) = tang η v := by
  exact GlobalTheory.OmegaFrobenius.unrealify_realify (tang η v)

theorem norm_sq_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    ‖tangL hη v‖ ^ 2 = ‖v.1‖ ^ 2 + (‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2) := by
  have hη1 : ‖(η : ℂ)‖ = 1 := by rcases hη with rfl | rfl <;> simp
  have e1 : ‖tangL hη v‖ ^ 2 = ∑ i, ∑ j, ‖tang η v i j‖ ^ 2 := by
    have h := norm_sq_unrealify (tangL hη v).1
    rw [unrealify_tangL] at h
    rw [← h, Submodule.coe_norm]
  have e2 : ‖v.1‖ ^ 2 = ∑ i, ∑ j, ‖unrealify v.1.1 i j‖ ^ 2 := by
    rw [← norm_sq_unrealify, Submodule.coe_norm]
  have e3 : ‖v.2.2‖ ^ 2 = ∑ j, ‖v.2.2 j‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  rw [e1, e2, e3]
  simp only [Fin.sum_univ_castSucc, tang, blk, Fin.lastCases_castSucc, Fin.lastCases_last, hv]
  have hc : ∀ z : ℂ, ‖z / (√2 : ℝ)‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  have hb : ∀ z : ℂ, ‖-(η : ℂ) * (starRingEnd ℂ) (z / (√2 : ℝ))‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_mul, norm_neg, hη1, one_mul, Complex.norm_conj, hc]
  have hd : ‖((v.2.1 : ℝ) : ℂ) * Complex.I‖ ^ 2 = ‖v.2.1‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  simp only [hb, hc, hd, Finset.sum_add_distrib]
  linarith [Finset.sum_div Finset.univ (fun x => ‖v.2.2.ofLp x‖ ^ 2) (2 : ℝ)]

theorem tangL_surjective {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Function.Surjective (tangL (k := k) hη) := by
  intro y
  set M := unrealify (y : EuclideanSpace ℝ (Fin (k + 1) × Fin (k + 1) × Bool)) with hMdef
  have hM := (GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (Hd_mul_self_eq_one hη)).1 y.2
  have e : ∀ i j, (starRingEnd ℂ) (M j i) * (if j = Fin.last k then (η : ℂ) else 1) +
      (if i = Fin.last k then (η : ℂ) else 1) * M i j = 0 := by
    intro i j
    have h := congrFun (congrFun hM i) j
    rwa [lie_entry, Matrix.zero_apply] at h
  let A : Matrix (Fin k) (Fin k) ℂ := fun i j => M i.castSucc j.castSucc
  have hA : GlobalTheory.OmegaFrobenius.realify k A ∈ lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) := by
    rw [GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive _ _ _ (by simp), GlobalTheory.OmegaFrobenius.unrealify_realify]
    ext i j
    have h := e i.castSucc j.castSucc
    simp [Fin.castSucc_ne_last] at h
    simp only [Matrix.mul_one, Matrix.one_mul]
    exact h
  have hll : (M (Fin.last k) (Fin.last k)).re = 0 := by
    have h := congrArg Complex.re (e (Fin.last k) (Fin.last k))
    rcases hη with rfl | rfl <;> simp at h <;> linarith
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  refine ⟨(⟨GlobalTheory.OmegaFrobenius.realify k A, hA⟩, (M (Fin.last k) (Fin.last k)).im,
    WithLp.toLp 2 (fun j => ((√2 : ℝ) : ℂ) * M (Fin.last k) j.castSucc)), ?_⟩
  apply Subtype.ext
  rw [← (GlobalTheory.OmegaFrobenius.realify (k + 1)).apply_symm_apply (y : EuclideanSpace ℝ _)]
  show GlobalTheory.OmegaFrobenius.realify (k + 1) (tang η _) = GlobalTheory.OmegaFrobenius.realify (k + 1) M
  congr 1
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · apply Complex.ext <;> simp [tang, blk, hll]
  · simp [tang, blk, hv, h2]
  · have h := e i.castSucc (Fin.last k)
    simp [Fin.castSucc_ne_last] at h
    simp [tang, blk, hv, h2]
    linear_combination -h
  · have hu : unrealify (GlobalTheory.OmegaFrobenius.realify k A) = A := GlobalTheory.OmegaFrobenius.unrealify_realify A
    simp only [tang, blk, Fin.lastCases_castSucc]
    exact congrFun (congrFun hu i) j

def tangIsom {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    WithLp 2 (lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × WithLp 2 (ℝ × EuclideanSpace ℂ (Fin k))) →ₗᵢ[ℝ]
      lieE (UH (Hd k η)) where
  toFun p := tangL hη (p.fst, p.snd.fst, p.snd.snd)
  map_add' p q := by rw [← map_add]; rfl
  map_smul' c p := by rw [← map_smul]; rfl
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact norm_sq_tangL hη _

theorem measurePreserving_of_isom {A B C D : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [MeasurableSpace C] [BorelSpace C] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (J : WithLp 2 (A × WithLp 2 (B × C)) →ₗᵢ[ℝ] D) (hs : Function.Surjective J) :
    MeasurePreserving (fun v : A × B × C => J (WithLp.toLp 2 (v.1, WithLp.toLp 2 v.2)))
      (volume.prod (volume.prod volume)) volume := by
  have h1 : MeasurePreserving (Prod.map (id : A → A) (WithLp.toLp 2 : B × C → WithLp 2 (B × C)))
      (volume.prod (volume.prod volume)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (WithLp.volume_preserving_toLp B C)
  have h2 := WithLp.volume_preserving_toLp A (WithLp 2 (B × C))
  have h3 := (LinearIsometryEquiv.ofSurjective J hs).measurePreserving
  exact h3.comp (h2.comp h1)

theorem measurePreserving_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    MeasurePreserving (tangL (k := k) hη) (volume.prod (volume.prod volume)) volume := by
  have hsurj : Function.Surjective (tangIsom (k := k) hη) := by
    intro y
    obtain ⟨v, rfl⟩ := tangL_surjective hη y
    exact ⟨WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2.1, v.2.2)), rfl⟩
  exact measurePreserving_of_isom (tangIsom hη) hsurj

theorem exists_tang_equiv : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  intro k η hk hη
  have hinj : Function.Injective (tangL (k := k) hη) := by
    refine (injective_iff_map_eq_zero (tangL hη)).2 fun v hv => ?_
    have h := norm_sq_tangL hη v
    rw [hv, norm_zero] at h
    have a := sq_nonneg ‖v.1‖
    have b := sq_nonneg ‖v.2.1‖
    have c := sq_nonneg ‖v.2.2‖
    have h1 : ‖v.1‖ ^ 2 = 0 := by nlinarith
    have h2 : ‖v.2.1‖ ^ 2 = 0 := by nlinarith
    have h3 : ‖v.2.2‖ ^ 2 = 0 := by nlinarith
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  let Lₗ := LinearEquiv.ofBijective (tangL hη) ⟨hinj, tangL_surjective hη⟩
  let L : Par k ≃L[ℝ] lieE (UH (Hd k η)) := Lₗ.toContinuousLinearEquiv
  refine ⟨L, fun v => unrealify_tangL hη v, fun ρ hρ => ?_⟩
  let e := L.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e (volume.prod (volume.prod volume)) volume :=
    ⟨(measurePreserving_tangL hη).measurable, (measurePreserving_tangL hη).map_eq⟩
  have hpre := hmp.measure_preimage_equiv (e '' Metric.ball (0 : Par k) ρ)
  rw [MeasurableEquiv.preimage_image] at hpre
  change volume (e '' Metric.ball (0 : Par k) ρ) = _
  rw [← hpre]
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hz : (0 : Par k) = (0, 0, 0) := rfl
  rw [hz, ← ball_prod_same, ← ball_prod_same, Measure.prod_prod, Measure.prod_prod, Real.volume_ball,
    InnerProductSpace.volume_ball (0 : EuclideanSpace ℂ (Fin k))]
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have hG : Real.Gamma (((2 * k : ℕ) : ℝ) / 2 + 1) = (k.factorial : ℝ) := by
    rw [show ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have hπ : √Real.pi ^ (2 * k) = Real.pi ^ k := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hf, hG, hπ]
  congr 1
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ (2 * k)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ρ)]
  congr 1
  ring

end GlobalTheory.TubeLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLattice
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowFrame

theorem one_mem_ddS_zpow (D : D7) (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hI0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    rw [Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hI1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hJ0 : ddS D ^ n ≠ 0 := pow_ne_zero _ hI0
  have hJ1 : ddS D ^ n ≤ 1 := pow_le_one' hI1 n
  rw [zpow_neg, zpow_natCast]
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹ := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = ddS D ^ n * (ddS D ^ n)⁻¹ :=
          (mul_inv_cancel₀ hJ0).symm
      _ ≤ 1 * (ddS D ^ n)⁻¹ := by gcongr
      _ = (ddS D ^ n)⁻¹ := one_mul _
  exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)

theorem frame_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) :
    IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  rintro ⟨-, ⟨-, -, hlift, -⟩, hX⟩ a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact hlift.1
  · have e : frame (lf D F0) i.castSucc = F0.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : F0.e i ∈ XS D F0 := by
      apply Submodule.subset_span
      refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
        rw [Nat.cast_sub i.isLt.le]
      rw [hk]
      exact one_mem_ddS_zpow D _
    rw [← hX] at hmem
    exact hmem.1

end GlobalTheory.Unfold.RowFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWordStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrame_mem_rowLattices_of_word : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ := by
  first | exact @GlobalTheory.RowFrame.frame_mem_rows | exact GlobalTheory.RowFrame.frame_mem_rows | (intros; apply GlobalTheory.RowFrame.frame_mem_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermuteStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_permute : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (s : Equiv.Perm (Fin n)), (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → StrictAnti (lam ∘ s) → IsHCU ε lam σ → IsHCDS (ε ∘ s) (lam ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) := by
  first | exact @GlobalTheory.DSSU.Chamber.vChamber | exact GlobalTheory.DSSU.Chamber.vChamber | (intros; apply GlobalTheory.DSSU.Chamber.vChamber <;> assumption)
end

