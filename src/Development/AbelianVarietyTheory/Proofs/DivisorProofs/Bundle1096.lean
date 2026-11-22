import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

theorem exists_monotone_blockFun (S : Set ℕ) :
    ∃ f : ℕ → ℕ, Monotone f ∧ ∀ i j : ℕ, (∃ s ∈ S, j < s ∧ s ≤ i) ↔ f j < f i := by
  classical
  refine ⟨fun i => ((Finset.range (i + 1)).filter (· ∈ S)).card, ?_, ?_⟩
  · intro a b hab
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    exact Finset.range_subset_range.2 (by omega)
  · intro i j
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      refine Finset.card_lt_card ⟨Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)), ?_⟩
      intro h
      have : s ∈ (Finset.range (j + 1)).filter (· ∈ S) := h (by simp [hs]; omega)
      simp at this
      omega
    · intro h
      by_contra hne
      refine absurd h (not_lt.2 (Finset.card_le_card ?_))
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
      refine ⟨?_, hs.2⟩
      by_contra h'
      exact hne ⟨s, hs.2, by omega, by omega⟩

theorem exists_blockLower_mul_blockUpper :
    ∀ (A : Type) [CommRing A] (N : ℕ) (S : Set ℕ) (g : GL (Fin N) A), (∀ (k : ℕ) (hk : k ≤ N), IsUnit (g.1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L b : GL (Fin N) A, g = L * b ∧ (∀ i j : Fin N, ¬ (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → L.1 i j = (1 : Matrix (Fin N) (Fin N) A) i j) ∧ ∀ i j : Fin N, (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → b.1 i j = 0 := by
  intro A _ N S g hm
  obtain ⟨l, u, hl0, hl1, hu, hg⟩ := exists_lower_mul_upper_of_leading_minors N g.1 hm
  obtain ⟨f₀, hf, hS⟩ := exists_monotone_blockFun S
  let f : Fin N → ℕ := fun i => f₀ i
  have hlt : ∀ i j : Fin N, f i < f j → i < j := fun i j h => hf.reflect_lt h
  let d : Matrix (Fin N) (Fin N) A := Matrix.of fun i j => if f i = f j then l i j else 0
  have hdd : d.det = 1 := det_eq_one_of_lower_unitriangular d
    (fun i j h => by simp [d, hl0 i j h]) (fun i => by simp [d, hl1])
  have hdu : IsUnit d.det := by rw [hdd]; exact isUnit_one
  have hld : l.det = 1 := det_eq_one_of_lower_unitriangular l hl0 hl1
  have hd1 : d.BlockTriangular f := fun i j h => by simp [d, h.ne']
  have hd2 : d.BlockTriangular (OrderDual.toDual ∘ f) := fun i j h => by
    have h' : f i < f j := h
    simp [d, h'.ne]
  letI := Matrix.invertibleOfIsUnitDet d hdu
  have hi1 := Matrix.blockTriangular_inv_of_blockTriangular hd1
  have hi2 := Matrix.blockTriangular_inv_of_blockTriangular hd2
  have hLu : IsUnit (l * d⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hld, one_mul]
    exact Matrix.isUnit_nonsing_inv_det d hdu
  obtain ⟨L, hL⟩ := hLu
  have hb : (L⁻¹ * g).1 = d * u := by
    have : g.1 = L.1 * (d * u) := by
      rw [hL, hg, Matrix.mul_assoc, ← Matrix.mul_assoc d⁻¹, Matrix.nonsing_inv_mul _ hdu,
        Matrix.one_mul]
    rw [Units.val_mul, this, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨L, L⁻¹ * g, by rw [mul_inv_cancel_left], ?_, ?_⟩
  · intro i j hij
    rw [hS] at hij
    have hij' : f i ≤ f j := not_lt.1 hij
    rw [hL, ← Matrix.mul_nonsing_inv d hdu, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases lt_trichotomy (f k) (f j) with h | h | h
    · rw [hi2 (i := k) (j := j) h, mul_zero, mul_zero]
    · by_cases h' : f i = f k
      · simp [d, h']
      · have : l i k = 0 := hl0 i k (hlt _ _ (lt_of_le_of_ne (h ▸ hij') h'))
        simp [d, this]
    · rw [hi1 (i := k) (j := j) h, mul_zero, mul_zero]
  · intro i j hij
    rw [hS] at hij
    have hu' : u.BlockTriangular f := fun i j h => hu (hlt _ _ h)
    rw [hb]
    exact (hd1.mul hu') hij

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem re_inner_apply_le_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (R : ℝ)
    (hR : ∀ (x : ℝ) (v : E), v ≠ 0 → T v = (x : ℂ) • v → x ≤ R) (y : E) :
    (inner ℂ y (T y)).re ≤ R * (inner ℂ y y).re := by
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  set b := hT.eigenvectorBasis hn
  set ev := hT.eigenvalues hn
  have hb : ∀ i, T (b i) = ((ev i : ℝ) : ℂ) • b i := fun i => hT.apply_eigenvectorBasis hn i
  have hle : ∀ i, ev i ≤ R := fun i => hR _ _ (b.orthonormal.ne_zero i) (hb i)
  have h3 : ∀ i, inner ℂ y (b i) * inner ℂ (b i) y = ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm (b i) y, Complex.norm_conj]
    first
      | (rw [Complex.mul_conj']; push_cast; rfl)
      | (rw [mul_comm, Complex.conj_mul']; push_cast; rfl)
  have h1 : inner ℂ y (T y) = ∑ i, ((ev i * ‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y (T y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT (b i) y, hb i, inner_smul_left, Complex.conj_ofReal, mul_left_comm, h3 i]
    push_cast; ring
  have h2 : inner ℂ y y = ∑ i, ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y y]
    exact Finset.sum_congr rfl fun i _ => h3 i
  rw [h1, h2, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hle i) (by positivity)

section Block

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def blockSub (s : ι → Bool) (U : Submodule ℂ M) : Submodule ℂ (ι → M) where
  carrier := {y | ∀ c, y c ∈ U ∧ (s c = false → y c = 0)}
  add_mem' {x y} hx hy c := ⟨U.add_mem (hx c).1 (hy c).1, fun h => by simp [(hx c).2 h, (hy c).2 h]⟩
  zero_mem' c := ⟨U.zero_mem, fun _ => rfl⟩
  smul_mem' r x hx c := ⟨U.smul_mem r (hx c).1, fun h => by simp [(hx c).2 h]⟩

def blockOp (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) : blockSub s U →ₗ[ℂ] blockSub s U where
  toFun y := ⟨fun a => if s a = true then ∑ b, F a b (y.1 b) else 0, fun c => by
    refine ⟨?_, fun h => by simp [h]⟩
    show (if s c = true then ∑ b, F c b (y.1 b) else 0) ∈ U
    split_ifs with hc
    · refine U.sum_mem fun b _ => ?_
      by_cases hb : s b = true
      · exact hst c b (hc.trans hb.symm) _ (y.2 b).1
      · rw [(y.2 b).2 (by simpa using hb), map_zero]; exact U.zero_mem
    · exact U.zero_mem⟩
  map_add' y z := by
    ext a
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
    split_ifs <;> simp
  map_smul' r y := by
    ext a
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
    split_ifs <;> simp [Finset.smul_sum]

theorem blockOp_apply (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) (y : blockSub s U) (a : ι) :
    (blockOp s F U hst y : ι → M) a = if s a = true then ∑ b, F a b (y.1 b) else 0 := rfl

def blockCore (s : ι → Bool) (U : Submodule ℂ M) (ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hsym : ∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) (hpos : ∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) :
    InnerProductSpace.Core ℂ (blockSub s U) where
  inner y z := ∑ c, ip (y.1 c) (z.1 c)
  conj_inner_symm y z := by
    simp only [map_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun c _ => hsym _ (z.2 c).1 _ (y.2 c).1
  re_inner_nonneg y := by
    simp only [RCLike.re_to_complex, Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    by_cases h : y.1 c = 0
    · simp [h]
    · exact (hpos _ (y.2 c).1 h).le
  add_left y z w := by simp [Finset.sum_add_distrib]
  smul_left y z r := by simp [Finset.mul_sum]
  definite y h := by
    have h' : ∑ c, (ip (y.1 c) (y.1 c)).re = 0 := by rw [← Complex.re_sum, h]; rfl
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (ip (y.1 c) (y.1 c)).re := fun c _ => by
      by_cases h : y.1 c = 0
      · simp [h]
      · exact (hpos _ (y.2 c).1 h).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h'
    ext c
    by_contra hc
    exact (hpos _ (y.2 c).1 hc).ne' (hz c (Finset.mem_univ c))

end Block

theorem re_diag_le_of_eigen_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  intro ι M _ _ _ _ s F U R hU hR a ha u hu hu0 m hm
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := hU
  let cd := blockCore s U ip hsym hpos
  letI : NormedAddCommGroup (blockSub s U) := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (blockSub s U) := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ U := hfd
  haveI : FiniteDimensional ℂ (blockSub s U) := by
    let e : blockSub s U →ₗ[ℂ] (ι → U) :=
      { toFun := fun y c => ⟨y.1 c, (y.2 c).1⟩
        map_add' := fun y z => rfl
        map_smul' := fun r y => rfl }
    exact Module.Finite.of_injective e
      (fun y z h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hinner : ∀ y z : blockSub s U, inner ℂ y z = ∑ c, ip (y.1 c) (z.1 c) := fun _ _ => rfl
  have key : ∀ (y z : blockSub s U) (c b : ι),
      ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) =
        ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
    intro y z c b
    by_cases hc : s c = true
    · by_cases hb : s b = true
      · rw [if_pos hc, if_pos hb]
        exact hadj c b (hc.trans hb.symm) _ (y.2 b).1 _ (z.2 c).1
      · rw [if_pos hc, if_neg hb, (y.2 b).2 (by simpa using hb)]
        simp
    · rw [if_neg hc, (z.2 c).2 (by simpa using hc)]
      simp
  have hT : (blockOp s F U hst).IsSymmetric := by
    intro y z
    rw [hinner, hinner]
    simp only [blockOp_apply]
    have e1 : ∀ c, ip (if s c = true then ∑ b, F c b (y.1 b) else 0) (z.1 c) =
        ∑ b, ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) := by
      intro c; split_ifs <;> simp [map_sum]
    have e2 : ∀ b, ip (y.1 b) (if s b = true then ∑ c, F b c (z.1 c) else 0) =
        ∑ c, ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
      intro b; split_ifs <;> simp [map_sum]
    simp only [e1, e2, key]
    exact Finset.sum_comm
  have hR' : ∀ (x : ℝ) (v : blockSub s U), v ≠ 0 → blockOp s F U hst v = (x : ℂ) • v → x ≤ R := by
    intro x v hv hTv
    refine hR x v.1 (fun h => hv (Subtype.ext h)) (fun c => (v.2 c).1) (fun c => (v.2 c).2) fun c hc => ?_
    have := congrFun (congrArg Subtype.val hTv) c
    rw [blockOp_apply, if_pos hc] at this
    exact this
  have hmem : Pi.single a u ∈ blockSub s U := by
    intro c
    by_cases hc : c = a
    · subst hc; simp only [Pi.single_eq_same]; exact ⟨hu, fun h => by simp [ha] at h⟩
    · rw [Pi.single_eq_of_ne hc]; exact ⟨U.zero_mem, fun _ => rfl⟩
  set y0 : blockSub s U := ⟨Pi.single a u, hmem⟩
  have hy0 : (y0 : ι → M) = Pi.single a u := rfl
  have hTa : (blockOp s F U hst y0 : ι → M) a = m • u := by
    rw [blockOp_apply, if_pos ha, hy0, Finset.sum_eq_single a, Pi.single_eq_same, hm]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have i1 : inner ℂ y0 (blockOp s F U hst y0) = m * ip u u := by
    rw [hinner, Finset.sum_eq_single a, hTa, hy0, Pi.single_eq_same, map_smul, smul_eq_mul]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have i2 : inner ℂ y0 y0 = ip u u := by
    rw [hinner, Finset.sum_eq_single a, hy0, Pi.single_eq_same]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have hle := re_inner_apply_le_of_eigen hT R hR' y0
  rw [i1, i2] at hle
  have him : (ip u u).im = 0 := by
    have h := hsym u hu u hu
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have hp := hpos u hu hu0
  rw [Complex.mul_re, him, mul_zero, sub_zero] at hle
  exact le_of_mul_le_mul_right hle hp

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleOpenRestrict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace CanonLB

open TopForm LB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {f : X ⟶ Sp R} (e : Y ⟶ X) [IsOpenImmersion e]
  {d : ℕ} [SmoothOfRelativeDimension d f]

theorem comp_spMap_id (f : X ⟶ Sp R) : e ≫ f = (e ≫ f) ≫ spMap (RingHom.id R) := by
  simp [spMap]

theorem isFrame_pullForm_openImm {U : X.Opens} {ω : FormsOn f d U} (hω : IsFrame ω)
    {W : Y.Opens} (hW : IsAffineOpen W) (h : W ≤ e ⁻¹ᵁ U) :
    IsFrame (pullForm (comp_spMap_id e f) h ω) := by
  have hle : e ''ᵁ W ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  have h' : W ≤ e ⁻¹ᵁ (e ''ᵁ W) := (e.preimage_image_eq W).ge
  have hω' : IsFrame (resForm hle ω) := hω.res (hW.image_of_isOpenImmersion e) hle
  have key : pullForm (comp_spMap_id e f) h ω = pullForm (comp_spMap_id e f) h' (resForm hle ω) := by
    rw [pullForm_resForm]
  rw [key]
  have hiso : IsIso (e.appLE (e ''ᵁ W) W h') := by
    have : e.appLE (e ''ᵁ W) W h' = (e.appIso W).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [this]
    infer_instance
  have sq := appLE_comp_algX (comp_spMap_id e f) h'
  haveI : IsIso (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) := by
    simpa using hiso
  haveI : IsIso (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id]
    infer_instance
  have H : IsPushout (CommRingCat.ofHom (algX f (e ''ᵁ W))) (CommRingCat.ofHom (RingHom.id R))
      (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) (CommRingCat.ofHom (algX (e ≫ f) W)) := by
    refine IsPushout.of_vert_isIso ⟨?_⟩
    ext x
    exact RingHom.congr_fun sq x
  exact ⟨hW, hω'.gen.formMapSq (RingHom.id R) (e.appLE (e ''ᵁ W) W h').hom sq H⟩

abbrev OIdx (e : Y ⟶ X) (K : CanonLB f d) : Type :=
  Σ i : K.bundle.ι, {W : Y.Opens // IsAffineOpen W ∧ W ≤ e ⁻¹ᵁ K.bundle.U i}

def oBundle (e : Y ⟶ X) (K : CanonLB f d) : LB Y :=
  ZH.UFib.refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1) (fun a => a.2.2.2)

theorem resG_oBundle_g (K : CanonLB f d) (a b : OIdx e K)
    {W : Y.Opens} (h : W ≤ (oBundle e K).U a ⊓ (oBundle e K).U b) :
    resG Y h ((oBundle e K).g a b : Γ(Y, (oBundle e K).U a ⊓ (oBundle e K).U b)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W
        (h.trans (fun _ hy => ⟨a.2.2.2 hy.1, b.2.2.2 hy.2⟩))).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) := by
  simp only [oBundle, ZH.UFib.refinePull, res, pullU, Units.coe_map, MonoidHom.coe_coe]
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, resG]
  rw [← Functor.map_comp]
  rfl

theorem iSup_oIdx (K : CanonLB f d) : ⨆ a : OIdx e K, a.2.1 = ⊤ :=
  eq_top_iff.2 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart K.isLB (e y)
    obtain ⟨W, hW, hy, hsub⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := e ⁻¹ᵁ K.bundle.U i) hi
    exact Opens.mem_iSup.2 ⟨⟨i, W, hW, fun z hz => hsub hz⟩, hy⟩

def oChartPull (K : CanonLB f d) : ChartPull (oBundle e K) K.bundle e where
  idx a := a.1
  le a := a.2.2.2
  g y a b h h' := ZH.UFib.gm_refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1)
    (fun a => a.2.2.2) y a b h h'

variable [SmoothOfRelativeDimension d (e ≫ f)]

theorem resForm_pullForm_om (K : CanonLB f d) (a b : OIdx e K) {W : Y.Opens} (hW : IsAffineOpen W)
    (ha : W ≤ a.2.1) (hb : W ≤ b.2.1) (h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1)) :
    resForm hb (pullForm (comp_spMap_id e f) b.2.2.2 (K.om b.1)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W h).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) •
        resForm ha (pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)) := by
  have hfa := isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2
  have h₁ := (K.isFrame a.1).coeff_pullForm (comp_spMap_id e f) a.2.2.2 hfa inf_le_left ha h
    (resForm inf_le_right (K.om b.1))
  rw [pullForm_resForm] at h₁
  rw [g_eq_ratio, resForm_pullForm]
  exact (hfa.coeff_smul_resForm hW ha _).symm.trans (congrArg (· • _) h₁)

def openImm (K : CanonLB f d) : CanonLB (e ≫ f) d where
  bundle := oBundle e K
  isLB := ZH.UFib.refinePull_isLB K.bundle K.isLB e _ _ _ (iSup_oIdx e K)
  affine a := a.2.2.1
  om a := pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)
  gen a := (isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2).gen
  trans a b W hW ha hb := by
    have h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1) :=
      le_inf (ha.trans a.2.2.2) (hb.trans b.2.2.2)
    exact (resForm_pullForm_om e K a b hW ha hb h).trans
      (congrArg (· • _) (resG_oBundle_g e K a b (le_inf ha hb)).symm)

end CanonLB

theorem cls_canonLB_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R)
    (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d (e ≫ f)] (K : CanonLB f d) (K' : CanonLB (e ≫ f) d),
    cls K'.bundle K'.isLB = CechPic.pull e (cls K.bundle K.isLB) := by
  intro R _ X Y f e _ d _ _ K K'
  have hp : (K.bundle.pull e).IsLB := Semi.LB.isLB_linComb K.isLB _ _
  calc cls K'.bundle K'.isLB = cls (K.openImm e).bundle (K.openImm e).isLB :=
        (cls_eq_iff _ _).2 (K'.lbIso (K.openImm e))
    _ = cls (K.bundle.pull e) hp :=
        (cls_eq_iff _ _).2 (LBIso.chartPull (K.oChartPull e)
          (Geo.Tor.chartPullPull K.bundle e e rfl) (K.lbIso K))
    _ = CechPic.pull e (cls K.bundle K.isLB) := cls_pull K.isLB e hp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ.Count

theorem card_sub_prod {ι β : Type} (p : β → Prop) :
    Nat.card {x : ι × β // p x.2} = Nat.card ι * Nat.card {y : β // p y} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ⟨fun x => (x.1.1, ⟨x.1.2, x.2⟩), fun x => ⟨(x.1, x.2.1), x.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem below_full {ι : Type} {N : ℕ} (τ : ι) (i j : Fin N) :
    Below (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd τ i j ↔ j < i :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => h₁.trans_le h₂, fun h => ⟨(τ, j.succ), rfl, by simp, by simpa using h⟩⟩

theorem card_lt (N : ℕ) : Nat.card {y : Fin N × Fin N // y.2 < y.1} = N * (N - 1) / 2 := by
  have h := Fintype.card_product_filter_lt (α := (Fin N)ᵒᵈ)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Nat.choose_two_right]
  rw [Fintype.card_orderDual, Fintype.card_fin] at h
  exact h

theorem card_full (ι : Type) [Fintype ι] (N : ℕ) :
    Nat.card {x : ι × Fin N × Fin N // x.2.2 < x.2.1} = dimFl ι N := by
  rw [card_sub_prod (fun y : Fin N × Fin N => y.2 < y.1), card_lt, Nat.card_eq_fintype_card, dimFl]

theorem card_block (N : ℕ) (j : Fin (N + 1)) :
    Nat.card {y : Fin N × Fin N // (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1} = j * (N - j) := by
  have hj := j.is_le
  have e : {y : Fin N × Fin N // (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1} ≃ Fin j × Fin (N - j) :=
    ⟨fun y => (⟨y.1.2, y.2.1⟩, ⟨y.1.1 - j, by have := y.1.1.2; have := y.2.2; omega⟩),
      fun z => ⟨(⟨z.2 + j, by have := z.2.2; omega⟩, ⟨z.1, by have := z.1.2; omega⟩), z.1.2, by simp⟩,
      fun y => by
        have := y.2.2
        ext <;> simp
        omega,
      fun z => by ext <;> simp⟩
  rw [Nat.card_congr e]
  simp

theorem card_cellVar (ι : Type) [Fintype ι] (N : ℕ) :
    Nat.card (CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd) = dimFl ι N ∧
    (∀ j : Fin (N + 1), Nat.card (CellVar (id : ι → ι) (fun _ => j)) = dimGr ι N j) ∧
    ∀ x : ι × Fin (N + 1), 0 < (x.2 : ℕ) → (x.2 : ℕ) < N →
      Nat.card (CellVar (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2)) + 1 = dimFl ι N := by
  refine ⟨?_, fun j => ?_, fun x h0 hN => ?_⟩
  · rw [← card_full]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => below_full _ _ _)
  · rw [dimGr, ← card_block, ← Nat.card_eq_fintype_card,
      ← card_sub_prod (fun y : Fin N × Fin N => (y.2 : ℕ) < j ∧ (j : ℕ) ≤ y.1)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨y.1, rfl, h⟩⟩)
  · rw [← card_full]
    obtain ⟨τ, m⟩ := x
    simp only at h0 hN
    let p : ι × Fin N × Fin N := (τ, ⟨m, hN⟩, ⟨m - 1, by omega⟩)
    let S : Set (ι × Fin N × Fin N) := {z | z.2.2 < z.2.1}
    have hp : p ∈ S := by
      change (m : ℕ) - 1 < m
      omega
    have h := Set.ncard_diff_singleton_add_one hp
    refine Eq.trans (congrArg (· + 1) ?_) h
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    obtain ⟨σ, i, j⟩ := z
    change _ ↔ (j : ℕ) < i ∧ ¬ (σ, i, j) = p
    constructor
    · rintro ⟨⟨⟨σ', k⟩, hk⟩, rfl, h₁, h₂⟩
      simp only at h₁ h₂
      refine ⟨h₁.trans_le h₂, fun e => hk ?_⟩
      simp only [p, Prod.mk.injEq, Fin.ext_iff] at e ⊢
      exact ⟨e.1, by omega⟩
    · rintro ⟨h₁, h₂⟩
      by_cases e : (σ, j.succ) = (τ, m)
      · refine ⟨⟨(σ, i.castSucc), fun e' => h₂ ?_⟩, rfl, by simpa using h₁, by simp⟩
        simp only [p, Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at e e' ⊢
        exact ⟨e.1, by omega, by omega⟩
      · exact ⟨⟨(σ, j.succ), e⟩, rfl, by simp, by simpa using h₁⟩

end GlobalTheory.FlagZ.Count
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependentStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent : ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K), P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 → LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  first | (exact @GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (exact GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (intros; apply GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  first | (exact @GlobalTheory.AwayPDen.charpoly_den_bounded) | (exact GlobalTheory.AwayPDen.charpoly_den_bounded) | (intros; apply GlobalTheory.AwayPDen.charpoly_den_bounded <;> assumption)
end

