import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
section
open Formalism.UG GlobalTheory.SatakeWeyl

open Matrix

namespace GlobalTheory.SatakeWeyl.InclusionMultiplication

variable {L : Type} [Field L] {n r : ℕ}

def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0

theorem incl_mul_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]

theorem mul_inclT_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix p (Fin r) L)
    (i : p) (j : Fin r) : (M * (incl L e)ᵀ) i (e j) = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem mul_inclT_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]

theorem inclT_mul_incl {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, he.eq_iff, Matrix.one_apply, eq_comm]

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ i.rev = j := by
    have := i.2
    rw [Fin.ext_iff, Fin.val_rev]; omega
  simp only [antiJ, this]

theorem antiJ_transpose : (antiJ L n)ᵀ = antiJ L n := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ, add_comm i.val j.val]

theorem antiJ_mul_incl {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    antiJ L n * incl L e = incl L e * antiJ L r := by
  ext a i
  have h1 : (antiJ L n * incl L e) a i = incl L e a.rev i := by
    simp [Matrix.mul_apply, antiJ_apply]
  have h2 : (incl L e * antiJ L r) a i = incl L e a i.rev := by
    simp [Matrix.mul_apply, antiJ_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  simp [incl, hr, Fin.rev_eq_iff]

theorem inclT_mul_antiJ {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this

def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ

theorem extendMatrixByIdentityAlongIndices_mul {e : Fin r → Fin n} (he : Function.Injective e) (M N : Matrix (Fin r) (Fin r) L) :
    ext1 e (M * N) = ext1 e M * ext1 e N := by
  have h : incl L e * (M - 1) * (incl L e)ᵀ * (incl L e * (N - 1) * (incl L e)ᵀ)
      = incl L e * ((M - 1) * (N - 1)) * (incl L e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl L e)ᵀ, inclT_mul_incl he, Matrix.one_mul]
  have h2 : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold ext1
  rw [add_mul, mul_add, mul_add, h, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b
  simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add,
    map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
    map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring

theorem extendMatrixByIdentityAlongIndices_unitary [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]

end GlobalTheory.SatakeWeyl.InclusionMultiplication

open GlobalTheory.SatakeWeyl.InclusionMultiplication in

theorem GlobalTheory.SatakeWeyl.embExists : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableBoundHilbertEisensteinTerms
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem norm_qPow_eq_exp {F : Type} [Field F] [NumberField F] (ξ : F) (w : Emb F → ℂ) :
    ‖qPow ξ w‖ = Real.exp (-(2 * Real.pi * ∑ i : Emb F, i ξ * (w i).im)) := by
  unfold qPow
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]

theorem norm_eTr_eq_one {F : Type} [Field F] [NumberField F] (y : F) : ‖eTr y‖ = 1 := by
  unfold eTr
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem exists_summable_bound_terms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t hc hτ
  obtain ⟨-, -, hpos, hsum⟩ := hc
  set w₀ : Emb F → ℂ := fun _ ↦ ((τ.im / 2 : ℝ) : ℂ) * Complex.I with hw₀
  have him : ∀ i, (w₀ i).im = τ.im / 2 := fun i ↦ by simp [hw₀]
  have hw : w₀ ∈ upperHalf F := fun i ↦ by rw [him i]; positivity
  have hs : Summable fun ξ : F ↦ ‖a ξ * qPow ξ w₀‖ := summable_norm_iff.mpr (hsum w₀ hw).summable
  refine ⟨fun ξ ↦ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖, hs.mul_left _, ?_⟩
  intro ξ z hz
  by_cases ha : a ξ = 0
  · simp [ha]
  have hnn : ∀ i : Emb F, 0 ≤ i ξ := fun i ↦ by
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact ((hpos ξ h0 ha).2 i).le
  set w : Emb F → ℂ := fun i ↦ τ + t * z i / (1 + z i * c) with hwdef
  have key : Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
      ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) = qPow ξ w := by
    rw [← Complex.exp_sum, ← Complex.exp_add, ← GlobalTheory.HilbFam.sum_realEmb_eq_trace F ξ]
    unfold qPow
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hwdef]
    ring
  have hq : ‖qPow ξ w‖ ≤ ‖qPow ξ w₀‖ := by
    rw [norm_qPow_eq_exp, norm_qPow_eq_exp]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [him i]
    exact mul_le_mul_of_nonneg_left (hz i).2 (hnn i)
  have hp : ‖∏ i : Emb F, (1 + z i * c)⁻¹ ^ k‖ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) := by
    rw [norm_prod, ← Finset.card_univ]
    have h := Finset.prod_le_prod (s := Finset.univ) (f := fun i : Emb F ↦ ‖(1 + z i * c)⁻¹ ^ k‖)
      (g := fun _ ↦ (2 : ℝ) ^ k) (fun i _ ↦ norm_nonneg _) (fun i _ ↦ by
        rw [norm_pow, norm_inv]
        apply pow_le_pow_left₀ (by positivity)
        have := (hz i).1
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith)
    rwa [Finset.prod_const] at h
  have e : a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))) =
      (∏ i : Emb F, (1 + z i * c)⁻¹ ^ k) * (eTr (ξ * x) * (a ξ * qPow ξ w)) := by
    rw [← key, Finset.prod_mul_distrib]
    ring
  rw [e, norm_mul, norm_mul, norm_eTr_eq_one, one_mul, norm_mul]
  show _ ≤ ((2 : ℝ) ^ k) ^ Fintype.card (Emb F) * ‖a ξ * qPow ξ w₀‖
  rw [norm_mul (a ξ)]
  gcongr

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimit
section
open IsLocalRing Polynomial CategoryTheory Limits

namespace GlobalTheory.TorsorColimElem

theorem exists_torsor_model_of_elements : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  intro ι _ _ _ R _ f hid hcomp B _ g hcompat hsurj hinj q hq D _ _ act hT
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (R i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le)
      map_id := fun i => by
        ext x
        simp [hid]
      map_comp := fun {i j k} a b => by
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply]
        exact (RingHom.congr_fun (hcomp i j k a.le b.le) x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of B
      ι := { app := fun i => CommRingCat.ofHom (g i)
             naturality := fun i j h => by
               ext x
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                 CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, F]
               exact RingHom.congr_fun (hcompat i j h.le) x } }
  have hc : IsColimit c := by
    haveI : ReflectsColimit F (forget CommRingCat) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      have hxy' : g i x = g j y := hxy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      have h0 : g k (f i k hik x - f j k hjk y) = 0 := by
        have e1 : g k (f i k hik x) = g i x := by rw [← hcompat i k hik]; rfl
        have e2 : g k (f j k hjk y) = g j y := by rw [← hcompat j k hjk]; rfl
        rw [map_sub, e1, e2, hxy', sub_self]
      obtain ⟨l, hkl, hl⟩ := hinj k _ h0
      refine ⟨l, homOfLE (hik.trans hkl), homOfLE (hjk.trans hkl), ?_⟩
      change f i l _ x = f j l _ y
      rw [map_sub, sub_eq_zero] at hl
      rw [← hcomp i k l hik hkl, ← hcomp j k l hjk hkl]
      exact hl
  have hT' : GlobalTheory.LocAcyc.IsZModTorsor B D q act := hT
  obtain ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩ :=
    @GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit ι _ _ F c hc q hq D _ ‹Algebra B D› act hT'
  exact ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩

end GlobalTheory.TorsorColimElem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldAffineOpenTransportStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_affineOpen_transport : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  first | exact @GlobalTheory.FieldTransport.exists_isField_transport | exact GlobalTheory.FieldTransport.exists_isField_transport | (intros; apply GlobalTheory.FieldTransport.exists_isField_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOCStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A], Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧ ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧ (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧ ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  first | exact @GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | exact GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | (intros; apply GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEq
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem sum_out_left_translate {A : Type} [Group A] (U : Subgroup A) [Fintype (A ⧸ U)] (F : A → ℂ)
    (hF : ∀ u ∈ U, ∀ a, F (a * u) = F a) (g : A) :
    ∑ y : A ⧸ U, F (g * y.out) = ∑ y : A ⧸ U, F y.out := by
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun y => ?_
  have h1 : (MulAction.toPerm g y : A ⧸ U) = ((g * y.out : A) : A ⧸ U) := by
    rw [MulAction.toPerm_apply, ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (g * y.out)
  rw [h1, hu, hF u u.2]

theorem unimodFin : UnimodFin := by
  intro A _ U V f hU hV hl hr
  haveI : U.FiniteIndex := ⟨hU⟩
  haveI : V.FiniteIndex := ⟨hV⟩
  letI : Fintype (A ⧸ U) := Fintype.ofFinite _
  letI : Fintype (A ⧸ V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have e1 : ∀ x : A ⧸ U, ∑ y : A ⧸ V, f (y.out⁻¹ * x.out) = ∑ y : A ⧸ V, f y.out⁻¹ := by
    intro x
    have := sum_out_left_translate V (fun a => f a⁻¹)
      (fun v hv a => by simp only [mul_inv_rev]; exact hl _ (V.inv_mem hv) _) x.out⁻¹
    simpa [mul_inv_rev] using this
  have e2 : ∀ y : A ⧸ V, ∑ x : A ⧸ U, f (y.out⁻¹ * x.out) = ∑ x : A ⧸ U, f x.out :=
    fun y => sum_out_left_translate U f hr _
  have := Finset.sum_comm (s := (Finset.univ : Finset (A ⧸ U))) (t := (Finset.univ : Finset (A ⧸ V)))
    (f := fun x y => f (y.out⁻¹ * x.out))
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact this

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem finite_surj_mod_ideal_exists_congr_one_mul_mem_range :
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B,
      Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) →
      ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  intro B C _ _ f hf J hs
  letI := f.toAlgebra
  haveI : Module.Finite B C := hf
  set P : Submodule B C := LinearMap.range (Algebra.linearMap B C) with hP
  have hle : (⊤ : Submodule B (C ⧸ P)) ≤ J • ⊤ := by
    rintro m -
    obtain ⟨c, rfl⟩ := P.mkQ_surjective m
    obtain ⟨b, hb⟩ := hs (Ideal.Quotient.mk _ c)
    have hy : c - f b ∈ J • (⊤ : Submodule B C) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp hb.symm
    have hfb : P.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
    have hc : P.mkQ c = P.mkQ (c - f b) := by rw [map_sub, hfb, sub_zero]
    rw [hc]
    have h1 : P.mkQ (c - f b) ∈ (J • (⊤ : Submodule B C)).map P.mkQ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    Module.Finite.fg_top hle
  refine ⟨r, hr1, fun c => ?_⟩
  have h := hr (P.mkQ c) trivial
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def] at hb
  exact hb.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBounds
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem natCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    refine le_trans (le_min ih (by simp)) (v.map_add _ _)

theorem intCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  cases n with
  | ofNat k => simpa using natCast_isInt v k
  | negSucc k =>
    rw [Int.cast_negSucc, v.map_neg]
    exact_mod_cast natCast_isInt v (k + 1)

theorem detDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C),
    IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧
    detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  intro C _ _ v p hp hv i d c G u hu
  obtain ⟨hhom, hint, -, -⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have h0 : 0 ≤ detDepth G u c := by
    unfold detDepth
    exact GlobalTheory.T.depth_nonneg_integral_operator_integral_vectors C v (Fin i) (fun _ => d) (fun _ => G) (fun _ => Fin i) (fun _ => u)
      (detPow C i c) (fun _ a e => hu.1 a e)
      (fun α => by obtain ⟨n, hn⟩ := hint α; rw [hn]; exact intCast_isInt v n)
  have h1 : detDepth G u c ≤ content v (detPow C i c) := by
    unfold detDepth
    exact GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent C v (Fin i) (fun _ => d) (fun _ => i) (fun _ => G) (fun _ => u)
      (detPow C i c) (i * c) hhom (fun _ => hu)
  exact ⟨h0, h1, h1.trans (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hv i c).1⟩

end GlobalTheory.FGDepth
end

