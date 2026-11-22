import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMemIsotropicFlagLevi
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.UAut.TorusLevi

theorem prodTens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have key : ∀ x : (A × B) ⊗[F] E, TensorProduct.prodLeft F F A B E x =
      (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x,
        Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp <;> rfl
    | tmul p e =>
      obtain ⟨p₁, p₂⟩ := p
      simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [key, key, a, b]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem adele_ext {z z' : AF F ⊗[F] E} (a : ∀ w, compInf F E w z = compInf F E w z')
    (b : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z') : z = z' := by
  classical
  have key : ∀ x : AF F ⊗[F] E, ∀ w : InfinitePlace F,
      TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)
        (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) x) w = compInf F E w x := by
    intro x w
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [map_zero (compInf F E w)]
      erw [map_zero]
      try erw [map_zero]
      try rfl
    | tmul p e => rfl
    | add x y hx hy =>
      rw [map_add (compInf F E w), ← hx, ← hy]
      erw [map_add, map_add]
      try rfl
  have hinf : Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z' := by
    apply (TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)).injective
    funext w
    rw [key, key, a]
  exact prodTens_ext hinf b

theorem exists_diagonal (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (s : Fin r → ℝ) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    ∃ δ : Fin r → AF F ⊗[F] E, (matHom _ σ J a).1 * adMat F Z = adMat F Z * diagonal δ := by
  classical
  have hR : ∀ w : InfinitePlace F, w.IsReal := fun w => h.1.isReal w
  let c : Fin r → Ainf F := fun i w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hR w)).symm (s i)
  refine ⟨fun i => (pairA F (c i) 1 : AF F) ⊗ₜ[F] (1 : E), ?_⟩
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  refine adele_ext (fun w => ?_) ?_
  · obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have harch : ∀ k l, archMat σ J τ (projArch σ J w a) k l =
        infEmb τ (compInf F E w ((matHom _ σ J a).1 k l)) := by
      intro k l
      show infEmb τ (((matHom _ σ J (projArch σ J w a)) : Matrix (Fin n) (Fin n) _) k l) = _
      rw [matHom_projArch]
      rfl
    have hZ : ∀ k l, infEmb τ (compInf F E w (inclR (F := F) (AF F) (Z k l))) = τ.1 (Z k l) := by
      intro k l
      simp [compInf, inclR, infEmb_tmul]
    have hev : evInf F w (pairA F (c j) 1) = c j w := rfl
    have hc : infEmb τ (compInf F E w ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E))) = (s j : ℂ) := by
      simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, hev, infEmb_tmul, map_one, mul_one]
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hR w),
        ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hR w), RingEquiv.apply_symm_apply]
    have hij := congrFun (congrFun (hs w τ) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hij
    simp only [map_sum, map_mul, Matrix.map_apply, hZ, hc, ← harch]
    simpa only [Matrix.map_apply] using hij
  · have hfin : ∀ k l, (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom ((matHom _ σ J a).1 k l) =
        (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l := fun k l =>
      congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l)
        (MonoidHom.mem_ker.mp ha)
    have hδ : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E)) = 1 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
      rfl
    simp only [map_sum, map_mul, hfin, hδ, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mem_parFlag (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (d : Fin r → ℕ) (s : Fin r → ℝ) (h0 : ∀ i, s i ≠ 0) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    a ∈ parFlag σ J Z d := by
  have hinv : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
    intro w τ
    have h1 : archMat σ J τ (projArch σ J w a⁻¹) * archMat σ J τ (projArch σ J w a) = 1 := by
      rw [← map_mul (archMat σ J τ), ← map_mul (projArch σ J w), inv_mul_cancel, map_one, map_one]
    have h2 : diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (h0 i))]
    calc archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1
        = archMat σ J τ (projArch σ J w a⁻¹) * (Z.map τ.1 *
            (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)))) := by
          rw [h2, Matrix.mul_one]
      _ = (archMat σ J τ (projArch σ J w a⁻¹) * (archMat σ J τ (projArch σ J w a) * Z.map τ.1)) *
            diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [hs w τ]
          simp only [Matrix.mul_assoc]
      _ = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨δ, hδ⟩ := exists_diagonal h ha Z s hs
  obtain ⟨δ', hδ'⟩ := exists_diagonal h (inv_mem ha) Z (fun i => (s i)⁻¹) hinv
  exact ⟨⟨diagonal δ, blockTriangular_diagonal δ, hδ⟩, diagonal δ', blockTriangular_diagonal δ', hδ'⟩

theorem torus_mem_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J _ r X Y d _ _ _ t a ht ha
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨mem_parFlag h ha1 X d t ht fun w τ => (ha2 w τ).1, ?_⟩
  refine mem_parFlag h ha1 Y d (fun i => (t i)⁻¹) (fun i => inv_ne_zero (ht i)) fun w τ => ?_
  simpa only [Complex.ofReal_inv] using (ha2 w τ).2.1

end GlobalTheory.UAut.TorusLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent resG)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.LB (resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem sub_mul_sub_eq_zero_of_closure {B : Type*} [CommRing B] (ψ : B →+* B) (s : Set B)
    (hs : Subring.closure s = ⊤) (H : ∀ x ∈ s, ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (x y : B) :
    (x - ψ x) * (y - ψ y) = 0 := by
  have step (x : B) (hx : ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (y : B) :
      (x - ψ x) * (y - ψ y) = 0 := by
    have hy : y ∈ Subring.closure s := hs ▸ Subring.mem_top y
    induction hy using Subring.closure_induction with
    | mem y hy => exact hx y hy
    | zero => simp
    | one => simp
    | add a b _ _ ha hb =>
      calc (x - ψ x) * (a + b - ψ (a + b)) = (x - ψ x) * (a - ψ a) + (x - ψ x) * (b - ψ b) := by
            rw [map_add]; ring
        _ = 0 := by rw [ha, hb, add_zero]
    | neg a _ ha =>
      calc (x - ψ x) * (-a - ψ (-a)) = -((x - ψ x) * (a - ψ a)) := by rw [map_neg]; ring
        _ = 0 := by rw [ha, neg_zero]
    | mul a b _ _ ha hb =>
      calc (x - ψ x) * (a * b - ψ (a * b)) =
            b * ((x - ψ x) * (a - ψ a)) + ψ a * ((x - ψ x) * (b - ψ b)) := by rw [map_mul]; ring
        _ = 0 := by rw [ha, hb]; ring
  have hx : x ∈ Subring.closure s := hs ▸ Subring.mem_top x
  revert y
  induction hx using Subring.closure_induction with
  | mem x hx => exact step x (H x hx)
  | zero => intro y; simp
  | one => intro y; simp
  | add a b _ _ ha hb =>
    intro y
    calc (a + b - ψ (a + b)) * (y - ψ y) = (a - ψ a) * (y - ψ y) + (b - ψ b) * (y - ψ y) := by
          rw [map_add]; ring
      _ = 0 := by rw [ha, hb, add_zero]
  | neg a _ ha =>
    intro y
    calc (-a - ψ (-a)) * (y - ψ y) = -((a - ψ a) * (y - ψ y)) := by rw [map_neg]; ring
      _ = 0 := by rw [ha, neg_zero]
  | mul a b _ _ ha hb =>
    intro y
    calc (a * b - ψ (a * b)) * (y - ψ y) =
          b * ((a - ψ a) * (y - ψ y)) + ψ a * ((b - ψ b) * (y - ψ y)) := by rw [map_mul]; ring
      _ = 0 := by rw [ha, hb]; ring

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

theorem toTsze_injective : Function.Injective (toTsze O M) :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom).1

theorem surjective_sec_zeroSec : Function.Surjective (sec (zeroSec O M)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O M).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (TrivSqZeroExt O M)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O M).toRingHom) := by
    rw [_root_.range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (TrivSqZeroExt O M)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem kappa_injective : Function.Injective (kappa O M) := by
  letI := (isChart O M).algebra
  letI := topModule O M
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := ((isChart O M).augCotEquiv (sec_hom _)).surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker ((isChart O M).aug (sec_hom _))).toCotangent_surjective y
  have h1 : (toTsze O M y).snd = 0 := by
    change (AugCot.lift _ (sndFn O M) (sndFn_der O M)) (((isChart O M).augCotEquiv
      (sec_hom _)).symm ((isChart O M).augCotEquiv (sec_hom _) _)) = 0 at hx
    rw [LinearEquiv.symm_apply_apply, AugCot.lift_toCotangent] at hx
    exact hx
  have h2 : (toTsze O M y).fst = 0 := by
    rw [← toO_sec]
    have : (isChart O M).aug (sec_hom _) y = 0 := y.2
    rw [IsChart.aug_apply] at this
    rw [this, map_zero]
  have h3 : (y : Γ((TM O M).left, ⊤)) = 0 :=
    toTsze_injective O M (by rw [map_zero]; ext <;> simp [h1, h2])
  have : y = 0 := Subtype.ext h3
  rw [this, map_zero, map_zero]

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

variable (M) in

abbrev preimTop (U : (Sp O).Opens) : (TM O M).left.Opens :=
  (𝟙 (TM O M).left) ⁻¹ᵁ ⊤ ⊓ (TM O M).hom ⁻¹ᵁ U

theorem mul_eq_zero_of_appLE {U : (Sp O).Opens} (hU : IsAffineOpen U)
    (hle : U ≤ sec (zeroSec O M) ⁻¹ᵁ (preimTop M U))
    (a b : Γ((TM O M).left, preimTop M U))
    (ha : (sec (zeroSec O M)).appLE (preimTop M U) U hle a = 0)
    (hb : (sec (zeroSec O M)).appLE (preimTop M U) U hle b = 0) : a * b = 0 := by
  obtain ⟨-, po⟩ := isAffineOpen_and_isPushout (IsPullback.id_horiz (TM O M).hom)
    (isAffineOpen_top (Sp O)) hU (isChart O M).affine (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top
  have hs := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let ψ := ((TM O M).hom.appLE U (preimTop M U) inf_le_right).hom.comp ((sec (zeroSec O M)).appLE (preimTop M U) U hle).hom
  have hψ₁ (r : Γ(Sp O, U)) : ψ ((TM O M).hom.appLE U (preimTop M U) inf_le_right r) =
      (TM O M).hom.appLE U (preimTop M U) inf_le_right r := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      ((TM O M).hom.appLE U (preimTop M U) inf_le_right r)) = _
    rw [appLE_base (sec_hom _) hle inf_le_right le_rfl, resG_self]
  have hψ₂ (x : Γ((TM O M).left, ⊤)) : ψ (Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left x) =
      Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left
        ((TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      (resG (TM O M).left (le_top : preimTop M U ≤ ⊤) x)) =
      resG (TM O M).left (le_top : preimTop M U ≤ ⊤) _
    rw [appLE_resG, ← resG_appLE (sec (zeroSec O M)) (le_top : U ≤ ⊤) le_top, appLE_resG]
    exact (resG_appLE (TM O M).hom (le_top : preimTop M U ≤ ⊤) le_top _).symm
  have h₀ (x y : Γ((TM O M).left, ⊤)) :
      (x - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) *
        (y - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top y)) = 0 := by
    apply toTsze_injective O M
    rw [map_mul, map_sub, map_sub, toTsze_base, toTsze_base, toO_sec, toO_sec, map_zero]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have key := sub_mul_sub_eq_zero_of_closure ψ _ hs (by
    rintro x (⟨x, rfl⟩ | ⟨r, rfl⟩) y (⟨y, rfl⟩ | ⟨s, rfl⟩)
    · rw [hψ₂, hψ₂, ← map_sub, ← map_sub, ← map_mul, h₀, map_zero]
    · rw [hψ₁, sub_self, mul_zero]
    · rw [hψ₁, sub_self, zero_mul]
    · rw [hψ₁, sub_self, zero_mul]) a b
  have ha' : ψ a = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle a) = 0
    rw [ha, map_zero]
  have hb' : ψ b = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle b) = 0
    rw [hb, map_zero]
  rwa [ha', hb', sub_zero, sub_zero] at key

variable {A : Over (Sp O)} [GrpObj A]

theorem preimage_le_of_zeroSec (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) {U : (Sp O).Opens}
    {W : A.left.Opens} (hU : U ≤ unitSec A ⁻¹ᵁ W) : (TM O M).hom ⁻¹ᵁ U ≤ z.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_zeroSec O M t
  have h₁ : s ∈ (sec (zeroSec O M) ≫ (TM O M).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := hU h₁
  rw [← show sec (zeroSec O M) ≫ z.left = unitSec A from congrArg (·.left) h] at h₂
  exact h₂

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

theorem eq_of_Phi_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M]
      [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A])
      (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  intro O _ A _ hq M _ _ _ _ z z' h h' hΦ
  have hq' : (conormal (sec η[A])).IsQuasicoherent := hq
  have hglob (w : Γ(conormal (sec η[A]), ⊤)) : (cotMap z h).app ⊤ w = (cotMap z' h').app ⊤ w :=
    kappa_injective O M ((Phi_apply z h w).symm.trans ((hΦ w).trans (Phi_apply z' h' w)))
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app (conormal (sec η[A]))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) (conormal (sec η[A]))
  have hcot : cotMap z h = cotMap z' h' := by
    apply (GlobalTheory.OmegaGlobal.map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) _ _).1
    ext s
    exact hglob s
  have hz : sec (zeroSec O M) ≫ z.left = unitSec A := congrArg (·.left) h
  have hz' : sec (zeroSec O M) ≫ z'.left = unitSec A := congrArg (·.left) h'
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_)
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom η[A]) (V := ⊤) (x := (TM O M).hom t) trivial
  have hT : IsAffineOpen (preimTop M U) := (isAffineOpen_and_isPushout
    (IsPullback.id_horiz (TM O M).hom) (isAffineOpen_top (Sp O)) c.affine_base (isChart O M).affine
    (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top).1
  have kz : preimTop M U ≤ z.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z h c.le)
  have kz' : preimTop M U ≤ z'.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z' h' c.le)
  have c₀ : IsChart (TM O M).hom (sec (zeroSec O M)) U (preimTop M U) :=
    ⟨c.affine_base, hT, fun x hx => ⟨trivial,
      (le_preimage_iff (π := (TM O M).hom) (sec_hom (zeroSec O M))).2 le_rfl hx⟩, inf_le_right⟩
  have e : z.left.appLE W (preimTop M U) kz = z'.left.appLE W (preimTop M U) kz' := by
    ext f
    rw [← sub_eq_zero]
    have ha : (sec (zeroSec O M)).appLE (preimTop M U) U c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, appLE_appLE hz kz c₀.le c.le, appLE_appLE hz' kz' c₀.le c.le, sub_self]
    have hd : d (sec_hom (zeroSec O M)) c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, ← cotMap_d z h c.le c₀.le kz f, ← cotMap_d z' h' c.le c₀.le kz' f, hcot,
        sub_self]
    letI := c₀.algebra
    have h₁ : AugCot.d (c₀.aug (sec_hom _))
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 :=
      (c₀.ofAugCot_bijective (sec_hom _)).1 (by rw [c₀.ofAugCot_d, map_zero]; exact hd)
    have h₂ := (AugCot.d_eq_zero_iff _ _).1 h₁
    rw [show c₀.aug (sec_hom _) _ = 0 from ha, map_zero, sub_zero] at h₂
    have hsq : RingHom.ker (c₀.aug (sec_hom (zeroSec O M))) ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha' b hb'
      exact (Ideal.mem_bot).2 (mul_eq_zero_of_appLE c.affine_base c₀.le a b ha' hb')
    rw [hsq] at h₂
    exact (Ideal.mem_bot).1 h₂
  refine ⟨preimTop M U, ⟨trivial, hU⟩, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT kz, ← c.affine.SpecMap_appLE_fromSpec _ hT kz', e]

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubBundleCurvatureRankOneStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_bundle_curvature_rank_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (u : m → ℂ) (hu : u ≠ 0) (ξ η : V), chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧ chernOne (gramQ H) z ξ η = chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η := by
  first | exact @GlobalTheory.LineRankTwo.chernOne_sub_quot_line | exact GlobalTheory.LineRankTwo.chernOne_sub_quot_line | (intros; apply GlobalTheory.LineRankTwo.chernOne_sub_quot_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleCurvatureFormulaStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_curvature_formula : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := by
  first | exact @GlobalTheory.SubGauss.curv_gramS | exact GlobalTheory.SubGauss.curv_gramS | (intros; apply GlobalTheory.SubGauss.curv_gramS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMulStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupAverage_prod_mul_eq_mul : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  first | exact @GlobalTheory.AvgProd.avg_prod | exact GlobalTheory.AvgProd.avg_prod | (intros; apply GlobalTheory.AvgProd.avg_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPolarisedTopChernCoeffTransgressionTelescope
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityLinear
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem cotMap_res_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → ∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w := by
  intro p O _ G A _ t hnat n w
  have key : (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))).comp (univ G (n + 1)) =
      (univ G n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
    ext a
    · simp [univ]
    · simp [univ]
  have hz : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1)) = spOver (univ G n) ≫ t.y n := by
    have e1 : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) =
        spOver (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))) := rfl
    rw [← Category.assoc, e1, spOver_comp, key, ← spOver_comp, Category.assoc, t.res n]
  have h0 := zeroSec_spOver_y t (n + 1) _ (fst_comp_univ (G := G) (n + 1))
  have h1 : zeroSec O _ ≫ (GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1))) = η[A] := by
    rw [hz]; exact zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)
  have := hnat _ _ (GlobalTheory.PDiv.cotMap (G.res n)) _ h0 h1 w
  unfold cn
  rw [← this]
  have hP : ∀ {z z' : TM O (GlobalTheory.PDiv.Cot O (G.A n)) ⟶ A} (e : z = z') h h', Phi z h = Phi z' h' := by
    rintro _ _ rfl _ _; rfl
  exact congrArg (fun f => f w) (hP hz _ _)

end GlobalTheory.SqZeroPt
end

