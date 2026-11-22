import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceDiv

section Abstract

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem single_mem (j i : n) : (Pi.single j (1 : R) : n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simpa using O.one_mem
  · simpa [Pi.single_eq_of_ne h] using O.zero_mem

theorem exists_factor (P Q : Matrix n n R)
    (H : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ P.mulVec y = Q.mulVec z) :
    ∃ M : Matrix n n O, P = Q * M.map O.subtype := by
  choose z hz1 hz2 using fun j => H (Pi.single j 1) (single_mem O j)
  refine ⟨Matrix.of fun i j => ⟨z j i, hz1 j i⟩, ?_⟩
  ext i j
  have := congrFun (hz2 j) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this]
  rfl

theorem mem_range_of_mul_eq_one (M N : Matrix n n O) (h : M.map O.subtype * N.map O.subtype = 1) :
    ∃ k ∈ (Formalism.UG.bc (n := n) O.subtype).range, k.1 = M.map O.subtype := by
  have h1 : M * N = 1 := by
    apply Matrix.map_injective O.subtype_injective
    simp only [Matrix.map_mul]
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨_, ⟨⟨M, N, h1, mul_eq_one_comm.1 h1⟩, rfl⟩, rfl⟩

theorem double_coset (B m T T' : Matrix n n R) (hT : T' * T = 1)
    (h1 : ∀ z : n → R, (∀ i, z i ∈ O) → ∀ i, B.mulVec z i ∈ O)
    (h2 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ y = B.mulVec z)
    (h3 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ m.mulVec y = (B * T).mulVec z)
    (h4 : ∀ z : n → R, (∀ i, z i ∈ O) → ∃ y : n → R, (∀ i, y i ∈ O) ∧ m.mulVec y = (B * T).mulVec z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := n) O.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := n) O.subtype).range,
      m = k₁.1 * T * k₂.1 := by
  obtain ⟨B0, hB0⟩ := exists_factor O B 1 fun y hy => ⟨_, h1 y hy, by rw [Matrix.one_mulVec]⟩
  rw [Matrix.one_mul] at hB0
  obtain ⟨C, hC⟩ := exists_factor O 1 B fun y hy => by rw [Matrix.one_mulVec]; exact h2 y hy
  obtain ⟨M, hM⟩ := exists_factor O m (B * T) h3
  obtain ⟨N, hN⟩ := exists_factor O (B * T) m fun z hz => (h4 z hz).imp fun y hy => ⟨hy.1, hy.2.symm⟩
  have hCB : C.map O.subtype * B = 1 := mul_eq_one_comm.1 hC.symm
  have hinv : T' * C.map O.subtype * (B * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B, hCB, Matrix.one_mul, hT]
  have hMN : M.map O.subtype * N.map O.subtype = 1 := by
    have e : B * T * (M.map O.subtype * N.map O.subtype) = B * T := by
      rw [← Matrix.mul_assoc, ← hM, ← hN]
    calc _ = T' * C.map O.subtype * (B * T) * (M.map O.subtype * N.map O.subtype) := by
          rw [hinv, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc, e, hinv]
  obtain ⟨k₁, hk₁, e₁⟩ := mem_range_of_mul_eq_one O B0 C (by rw [← hB0, ← hC])
  obtain ⟨k₂, hk₂, e₂⟩ := mem_range_of_mul_eq_one O M N hMN
  exact ⟨k₁, hk₁, k₂, hk₂, by rw [e₁, e₂, ← hB0, hM]⟩

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sgT_mem_intA (v : HeightOneSpectrum (𝓞 F)) {y : Fv F v ⊗[F] E} (hy : y ∈ ordAt E v) :
    sgT E v y ∈ intA F E := by
  refine (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).2 fun w => ?_
  by_cases h : w = v
  · subst h; rwa [evF_sgT_self]
  · rw [evF_sgT_ne h]; exact zero_mem _

theorem sgT_mem_lamHat [StarRing E] (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    (fun i => sgT E v (y i)) ∈ lamHat F V := by
  refine (mem_lamHat_iff V _).2 fun w => ?_
  by_cases h : w = v
  · subst h; simpa only [evF_sgT_self] using hy
  · simp only [evF_sgT_ne h]; exact zero_mem _

omit [NumberField E] in
theorem evF_mulVec {n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F)) {f : Af F ⊗[F] E} (hf : evF E v f = 1)
    (A : Matrix n n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    (fun a => evF E v (f * A.mulVec z a)) = (A.map (evF E v)).mulVec fun i => evF E v (z i) := by
  funext a
  rw [map_mul, hf, one_mul, RingHom.map_mulVec]
  rfl

theorem double_coset_of_divG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  intro F E _ _ _ _ _ _ hc V v e h ϖ d g he hh hϖ ⟨B, h1, h2, h3, h4⟩
  have he1 := he.2.1
  have hfr : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y i ∈ ordAt E v) →
      h.1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := fun y hy => by
    refine (hh _).2 ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hy
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1.mulVec ((h⁻¹).1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1.mulVec (h.1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ y z : Fin V.rank → Af F ⊗[F] E,
      ((fun a => finP F E e * (finMat hc.sig V.gram g).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) →
      (locMat hc V v g).1.mulVec (fun i => evF E v (y i)) =
        (B.map (evF E v) * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec fun i => evF E v (z i) := by
    intro y z hyz
    rw [locMat_val, ← evF_mulVec v he1, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec (fun i => evF E v (z i)) =
        fun i => evF E v (finP F E (inclR (AF F) (ϖ ^ d i)) * z i) := by
      funext i
      rw [Matrix.mulVec_diagonal, map_mul, evF_finP_incl]
    rw [e2, ← evF_mulVec v he1]
    funext a
    rw [congrFun hyz a]
  refine double_coset (ordAt E v) ((h⁻¹).1 * B.map (evF E v)) _ _
    (Matrix.diagonal fun i => inclR (Fv F v) (ϖ ^ d i)⁻¹) ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ), map_one]
  · intro z hz
    have := (mem_lamHat_iff V _).1 (h1 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)) v
    rw [evF_mulVec v he1] at this
    simp only [evF_sgT_self] at this
    rw [← Matrix.mulVec_mulVec]
    exact (hh _).1 this
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h2 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← evF_mulVec v he1, ← hback' y]
    congr 1; funext a
    rw [← congrFun e2 a, map_mul, he1, one_mul, evF_sgT_self]
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h3 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro z hz
    obtain ⟨y, hy, e2⟩ := h4 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)
    refine ⟨(h⁻¹).1.mulVec fun i => evF E v (y i), (hh _).1 ((mem_lamHat_iff V _).1 hy v), ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback]

end GlobalTheory.PlaceDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Stab

open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

theorem isInt_mulVec {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((M *ᵥ x) i) :=
  isInt_iff.2 (show ∑ k, M i k * x k ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hM i k)) (isInt_iff.1 (hx k)))

theorem isInt_vecMul {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((x ᵥ* M) i) :=
  isInt_iff.2 (show ∑ k, x k * M k i ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hx k)) (isInt_iff.1 (hM k i)))

theorem map_mulVec' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (y : Fin n → R) : (fun i => f ((M *ᵥ y) i)) = M.map f *ᵥ fun i => f (y i) :=
  funext fun i => RingHom.map_mulVec f M y i

theorem dual_move {R K : Type} [CommRing R] [Field K] (c : R →+* R) (π : R →+* K) {n : ℕ}
    (G M N : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) K) (h : G * N = (M.map c)ᵀ * G) (y : Fin n → R) :
    (fun i => π (c ((M *ᵥ y) i))) ᵥ* (G.map π * β.1) =
      ((fun i => π (c (y i))) ᵥ* (G.map π * β.1)) ᵥ* ((β⁻¹).1 * N.map π * β.1) := by
  have hG : G.map π * N.map π = (M.map (π.comp c))ᵀ * G.map π := by
    rw [← Matrix.map_mul, h, Matrix.map_mul]
    rfl
  have hc := map_mulVec' (π.comp c) M y
  simp only [RingHom.comp_apply] at hc
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hG, Matrix.mul_assoc,
    ← Matrix.vecMul_mulVec, hc]

theorem split_move {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a b : R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, (a + b) * (M - 1) i j = (M - 1) i j) (y : Fin n → R) :
    (M.map f *ᵥ fun i => f (y i)) = ((fun i => f (a * (M *ᵥ y) i)) + fun i => f (b * (M *ᵥ y) i)) +
      (((fun i => f (y i)) - fun i => f (a * y i)) - fun i => f (b * y i)) := by
  have h1 : (a + b) • (M - 1) = M - 1 := Matrix.ext fun i j => h i j
  have h3 : (a + b) • (M *ᵥ y - y) = M *ᵥ y - y := by
    have := congrArg (· *ᵥ y) h1
    simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
  rw [← map_mulVec']
  funext i
  have h4 : (a + b) * ((M *ᵥ y) i - y i) = (M *ᵥ y) i - y i := congrFun h3 i
  simp only [Pi.add_apply, Pi.sub_apply, ← map_add, ← map_sub]
  congr 1
  linear_combination -h4

variable {D : D7}

theorem finPart_surj (z : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ a : AE D, finPart D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul α x => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem idem_mul_mem (V : HSp D) {a : AE D} (ha : a * a = a) {y : Fin V.rank → AE D}
    (hy : (fun i => finPart D (y i)) ∈ LamHat V) : (fun i => finPart D (a * y i)) ∈ LamHat V := by
  have h := GlobalTheory.SplitHeckeLabel.smul_mem_latHat (GlobalTheory.PlaceModel.latFrame V) (x := finPart D a)
    (y := fun i => finPart D (y i))
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
    (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hy)
  rw [GlobalTheory.PlaceModel.coe_latFrame] at h
  have e : (fun i => finPart D (a * y i)) = finPart D a • fun i => finPart D (y i) :=
    funext fun i => RingHom.map_mul _ _ _
  rw [e]
  exact h

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h1 : mt V g⁻¹ - 1 = -((mt V g - 1) * mt V g⁻¹) := by
    rw [Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  have h2 : (e + cA D e) • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1 := by
    rw [h1, smul_neg, ← Matrix.smul_mul, h]
  exact fun i j => congrFun (congrFun h2 i) j

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {V : HSp D}
  {β : GL (Fin V.rank) (Fv D.host.F v)}

theorem intM_of_stable (hπ : Chart e v π) (hβ : Frame V e π β) {g : GA D V}
    (h : ∀ y ∈ LamHat V, finMat D.sp.cm.sig V.gram g *ᵥ y ∈ LamHat V) : IntM (Ov D v) (rho V π β g).1 := by
  intro i j
  choose y hy using fun k => hπ.1 (β.1 k j)
  have hcol : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, Matrix.mulVec_single_one]
    rfl
  have h1 := (hβ y).2 fun k => by
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mulVec_single_one]
    exact intM_one k j
  have h2 := h _ h1
  rw [finMat_eq, ← map_mulVec'] at h2
  have h3 : mt V g *ᵥ (fun k => e * y k) = fun k => e * (mt V g *ᵥ y) k := Matrix.mulVec_smul _ e y
  rw [h3] at h2
  have h4 := (hβ _).1 h2 i
  rw [map_mulVec', hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h4
  rw [rho_val]
  exact h4

theorem stable_of_intM (he : IsSplitIdem D e) (hβ : Frame V e π β)
    (hd : ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j))
    {g : GA D V} (hg : SuppAt e V g) (h1 : IntM (Ov D v) (rho V π β g).1) (h2 : IntM (Ov D v) (rho V π β g⁻¹).1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ LamHat V) :
    finMat D.sp.cm.sig V.gram g *ᵥ z ∈ LamHat V := by
  choose y hy using fun k => finPart_surj (z k)
  obtain rfl : z = fun k => finPart D (y k) := funext fun k => (hy k).symm
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have a1 := idem_mul_mem V he.1 hz
  have a2 := idem_mul_mem V he'.1 hz
  have b1 : (fun i => finPart D (e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hβ _).2 fun i => ?_
    have := isInt_mulVec h1 ((hβ y).1 a1) i
    rwa [rho_val, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← map_mulVec'] at this
  have b2 : (fun i => finPart D (cA D e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hd _).2 fun i => ?_
    have := isInt_vecMul h2 ((hd y).1 a2) i
    rw [rho_val] at this
    exact (congrFun (dual_move (cA D) π (V.gram.map (incA D)) _ _ β (gram_mul_inv V g) y) i).symm ▸ this
  rw [finMat_eq, split_move (finPart D) e (cA D e) (mt V g) hg y]
  exact add_mem (add_mem b1 b2) (sub_mem (sub_mem hz a1) a2)

theorem finMat_mul_inv (g : GA D V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig V.gram g *ᵥ (finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y) = y := by
  rw [finMat_eq, finMat_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mulVec]

theorem mem_KsphC_iff_gInt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  intro D e v π he hπ V β hβ g hg
  have hd := GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ V β hβ
  unfold GInt
  rw [← map_inv]
  constructor
  · rintro ⟨-, h, -⟩
    exact ⟨intM_of_stable hπ hβ fun y hy => (h y).1 hy,
      intM_of_stable hπ hβ fun y hy => (h _).2 (by rw [finMat_mul_inv]; exact hy)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_GfC he hg, fun y => ⟨stable_of_intM he hβ hd hg h1 h2 y, fun hy => ?_⟩,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
    have h3 := stable_of_intM he hβ hd (suppAt_inv hg) h2 (by rw [inv_inv]; exact h1) _ hy
    have h4 := finMat_mul_inv g⁻¹ y
    rw [inv_inv] at h4
    rwa [h4] at h3

end GlobalTheory.SplitHecke.Stab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLamCTypeNormOne
section
noncomputable section

namespace GlobalTheory.TwU.RatNorm

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem frob_pow_int (X : Sys p) (v : X.Pl) (k : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ k) (algebraMap _ _ x) = algebraMap _ _ y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ]
    show (X.G.P.σ v ^ k) ((X.G.P.σ v) (algebraMap _ _ x)) = _
    rw [hy, hz]

theorem norm_twG_int_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    ‖twG X E v s (algebraMap _ _ x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := frob_pow_int X v s.val x
  have h := E.int (X.G.P.j v y)
  unfold twG
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hy, (X.G.P.setting v).ι_comp]
  exact h

theorem norm_twG_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    ‖twG X E v s (algebraMap _ _ (u : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_int_le X E v s (u : X.G.P.W v)
  have h2 := norm_twG_int_le X E v s ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have h3 : twG X E v s (algebraMap _ _ (u : X.G.P.W v)) * twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg (twG X E v s (algebraMap _ _ (u : X.G.P.W v))),
    norm_nonneg (twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) {y : X.G.P.Qq v} (hy : y ≠ 0) :
    ‖twG X E v s y‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p y := by
  haveI := (X.G.P.setting v).frac_alt
  have hp := (X.G.P.setting v).p_unif
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  rw [ordP_eq hp n u, map_mul, map_zpow₀, map_natCast, norm_mul, norm_twG_unit, one_mul, norm_zpow]

theorem zpow_sum_fin {ι : Type*} (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (f : ι → ℤ) :
    r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hr, ih]

theorem norm_lamC_type_normOne : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
    LamPos X E pos lam ρ → ∀ (e : D.what₂.Tau → ℤ) (z : D.host.E), z * D.host.conj z = 1 →
    ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ)‖ =
      ‖(p : ℂ_[p])‖ ^ (∑ v : X.Pl, (∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩)) *
        ordP (X.G.P.W v) p (ρ v z)) := by
  intro D p _ X E pos lam ρ hL e z hz
  have hp0 : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hmem : ∀ τ, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hprod : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => zpow_mem (hmem τ) _
  have h1 : TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) = ∏ τ, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ z) ^ e τ := by
    have e1 : (⟨∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ, hprod⟩ : TaylorLogMetric.Qbar) = ∏ τ, (⟨TaylorLogMetric.embT D τ z, hmem τ⟩ : TaylorLogMetric.Qbar) ^ e τ := by
      apply Subtype.ext
      push_cast
      rfl
    unfold TaylorLogMetric.lamC
    rw [dif_pos hprod, e1, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [dif_pos (hmem τ), map_zpow₀]
  have hρ : ∀ v, ρ v z * ρ v (D.host.conj z) = 1 := fun v => by rw [← map_mul, hz, map_one]
  have hρ0 : ∀ v, ρ v z ≠ 0 := fun v h => by have := hρ v; rw [h, zero_mul] at this; exact zero_ne_one this
  have hf : ∀ v s, ‖TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) z)‖ ^ e (pos ⟨v, s⟩) =
      ‖(p : ℂ_[p])‖ ^ ((if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩) * ordP (X.G.P.W v) p (ρ v z)) := by
    intro v s
    by_cases hs : IsOddPos s
    · rw [LamPos.odd X E pos lam ρ hL v s hs, if_pos hs, eq_inv_of_mul_eq_one_right (hρ v), map_inv₀, norm_inv, norm_twG X E v s (hρ0 v),
        inv_zpow', ← zpow_mul]
      congr 1
      ring
    · rw [LamPos.even X E pos lam ρ hL v s hs, if_neg hs, norm_twG X E v s (hρ0 v), ← zpow_mul]
      congr 1
      ring
  rw [h1, norm_prod]
  simp_rw [norm_zpow]
  rw [← Equiv.prod_comp pos, Fintype.prod_sigma]
  simp_rw [hf, Finset.sum_mul]
  rw [zpow_sum_fin _ _ hp0]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [zpow_sum_fin _ _ hp0]

end GlobalTheory.TwU.RatNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLogStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  first | exact @GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | exact GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | (intros; apply GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormDetLatticeBasisEqDetIdealNormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  first | exact @GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | exact GlobalTheory.DetBasisNorm.norm_det_eq_nrmId | (intros; apply GlobalTheory.DetBasisNorm.norm_det_eq_nrmId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PendTThFLtOfKapLawLt
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU

theorem pendT_ThF_lt_of_kapLawLt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; KapLawLt X ℂ_[p] (thFOf X pos F) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La') ∧ ∀ v, ∀ j < X.mm, XiEx X ℂ_[p] (thFOf X pos F) v j → XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j := by
  intro p _ X _ E hfin hst g hLT T pos F
  intro hK
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  have h1 : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La' := by
    rintro j hj ⟨c, L⟩ La' hL hL'
    change thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin (thFOf X pos F)) j (c, L) La' = _
    rw [thN_eq]
    generalize delt X hfin j c L = δ
    have hL2 : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul δ⁻¹ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ δ⁻¹ L).2 hL
    have := hK j hj c _ La' δ hL2 hL'
    rw [lsmul_lsmul_inv] at this
    exact this.symm
  refine ⟨h1, ?_⟩
  rintro v j hj ⟨Ξ, u, u', hu, hu', hΞ⟩
  refine ⟨Ξ, u, u', hu, hu', fun La La' hL hL' => ?_⟩
  rw [h1 j hj La La' hL hL']
  exact hΞ La La' hL hL'

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)), IsFrameAt V v h → ∀ g, (∀ w, w ≠ v → locMat hc V w g = 1) → (Stab hc V g ↔ h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range) := by
  first | exact @GlobalTheory.PlaceComp.StabLoc.stab_iff | exact GlobalTheory.PlaceComp.StabLoc.stab_iff | (intros; apply GlobalTheory.PlaceComp.StabLoc.stab_iff <;> assumption)
end

