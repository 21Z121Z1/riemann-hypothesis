import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AutomorphicArithmetic.ShortNorms.Primes
import Development.AutomorphicArithmetic.ShortNorms.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRel
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabFrame

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_mulVec_eq (σ : E →ₐ[F] E) {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E) (hN : N * B = 1) (x : Fin M → E)
    (hM : M' + 1 = M) (hB : ∀ j, hE σ J x (fun i => B i j) = 0) (hx : hE σ J x x ≠ 0) :
    (∀ z, hE σ J x (B *ᵥ z) = 0) ∧ ∀ y, hE σ J x y = 0 → B *ᵥ (N *ᵥ y) = y := by
  let φ : (Fin M → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := fun y z => by
        simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hinj : Function.Injective B.mulVecLin := fun z w h => by
    have := congrArg (N *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hN] using this
  have h1 : Module.finrank E (LinearMap.range B.mulVecLin) = M' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hlt : LinearMap.ker φ < ⊤ := lt_top_iff_ne_top.2 fun h => hx (by
    have : x ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    exact this)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_top, Module.finrank_fin_fun] at h2
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨fun z => hle ⟨z, rfl⟩, fun y hy => ?_⟩
  have : y ∈ LinearMap.range B.mulVecLin := heq ▸ hy
  obtain ⟨z, rfl⟩ := this
  simp [Matrix.mulVec_mulVec, hN]

theorem map_mulVec_tmul (R : Type) [CommRing R] [Algebra F R] {m n : ℕ} (C : Matrix (Fin m) (Fin n) E)
    (a : R) (z : Fin n → E) :
    C.map (inclR (F := F) R) *ᵥ (fun i => a ⊗ₜ[F] z i) = fun i => a ⊗ₜ[F] (C *ᵥ z) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]

variable [NumberField F]

theorem mulVec_mem_latHat {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) {S : Set (Fin n → E)}
    {T : Set (Fin m → E)} (h : ∀ z ∈ S, C *ᵥ z ∈ T) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E T := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h z hz, map_mulVec_tmul _ C a z⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_eq_of_mem_latHat {n : ℕ} (C : Matrix (Fin n) (Fin n) E) {S : Set (Fin n → E)}
    (h : ∀ z ∈ S, C *ᵥ z = z) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    rw [map_mulVec_tmul, h z hz]
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | neg y _ hy => rw [Matrix.mulVec_neg, hy]

theorem stabHat_iff {M M' : ℕ} (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E)
    (hN : N * B = 1) {P : Set (Fin M → E)} {L' : Set (Fin M' → E)} (h1 : ∀ z, z ∈ L' ↔ B *ᵥ z ∈ P)
    (h2 : ∀ y ∈ P, B *ᵥ (N *ᵥ y) = y) (a b : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (a' b' : Matrix (Fin M') (Fin M') (Af F ⊗[F] E)) (hb : b * a = 1) (hb' : a' * b' = 1)
    (hr : a * B.map (inclR (F := F) (Af F)) = B.map (inclR (F := F) (Af F)) * a') :
    StabHat F P a ↔ StabHat F L' a' := by
  set Bf := B.map (inclR (F := F) (Af F)) with hBf
  set Nf := N.map (inclR (F := F) (Af F)) with hNf
  have hNB : Nf * Bf = 1 := by
    rw [hBf, hNf, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm : ∀ z ∈ latHat F E L', Bf *ᵥ z ∈ latHat F E P := fun z hz =>
    mulVec_mem_latHat B (fun w hw => (h1 w).1 hw) hz
  have hNm : ∀ y ∈ latHat F E P, Nf *ᵥ y ∈ latHat F E L' := fun y hy =>
    mulVec_mem_latHat N (fun w hw => (h1 _).2 (by rw [h2 w hw]; exact hw)) hy
  have hBN : ∀ y ∈ latHat F E P, Bf *ᵥ (Nf *ᵥ y) = y := fun y hy => by
    rw [Matrix.mulVec_mulVec, hBf, hNf, ← Matrix.map_mul]
    exact mulVec_eq_of_mem_latHat _ (fun w hw => by rw [← Matrix.mulVec_mulVec]; exact h2 w hw) hy
  have hiff : ∀ z, z ∈ latHat F E L' ↔ Bf *ᵥ z ∈ latHat F E P := fun z =>
    ⟨hBm z, fun hz => by simpa [Matrix.mulVec_mulVec, hNB] using hNm _ hz⟩
  have hcomm : ∀ z, a *ᵥ (Bf *ᵥ z) = Bf *ᵥ (a' *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr]
  refine ⟨fun h z => ?_, fun h y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hiff, hiff, ← hcomm]
    exact h _
  · rw [← hBN y hy, hcomm]
    exact hBm _ ((h _).1 (hNm y hy))
  · have e1 : a' *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) = Nf *ᵥ (a *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hb', Matrix.one_mulVec]
    have e2 : y = Bf *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) := by
      have := congrArg (b *ᵥ ·) (hcomm (b' *ᵥ (Nf *ᵥ (a *ᵥ y))))
      simp only [e1, hBN _ hy] at this
      rw [Matrix.mulVec_mulVec _ b a, Matrix.mulVec_mulVec _ b a, hb, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
      exact this.symm
    rw [e2]
    exact hBm _ ((h _).2 (by rw [e1]; exact hNm _ hy))

def finPt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) : HA (Af F) σ J :=
  (⟨Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g), by
    have hg : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J g).1 * JR (AF F) J * (HA.mat (AF F) σ J g).1 =
      JR (AF F) J := (show HR (AF F) σ J from g).2
    have := GlobalTheory.UnitarySplit.map_cond _ _ _ (GlobalTheory.UnitarySplit.map_sig (sndA F) σ) (JR (AF F) J)
      (HA.mat (AF F) σ J g).1
    rw [hg, GlobalTheory.UnitarySplit.map_JR] at this
    exact this.symm⟩ : HR (Af F) σ J)

theorem map_snd_incl {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) :
    (C.map (inclR (F := F) (AF F))).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom =
      C.map (inclR (F := F) (Af F)) := by
  ext i j
  simp [inclR]

end Lin

theorem stab_iff_of_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  intro H F E _ _ _ _ _ σ hCM hu M M' J J' B x hM hJ hJ' hBJ hB hx L L' hL β hβ hxL hq hL' g g' hg hr
  let p := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hN : (J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)) * B = 1 := by
    rw [Matrix.mul_assoc, hBJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ'.2)]
  obtain ⟨k1, k2⟩ := exists_mulVec_eq σ J B _ hN (x 0) hM hB hx
  have h3 := (H F E σ hCM hu M J hJ L hL β hβ (x 0) hxL hq).2.2
  have hgf : finPt σ J g ∈ Hstab (Af F) σ J (fun _ => x 0) := by
    have e : (HA.mat (AF F) σ J g).1 *ᵥ (fun i => inclR (AF F) (x 0 i)) = fun i => inclR (AF F) (x 0 i) :=
      congrFun (MulAction.mem_stabilizer_iff.1 hg) 0
    have e' : (p ∘ fun i => inclR (AF F) (x 0 i)) = fun i => inclR (Af F) (x 0 i) := by
      funext i
      simp [p, inclR]
    refine MulAction.mem_stabilizer_iff.2 (funext fun _ => funext fun i => ?_)
    have := RingHom.map_mulVec p (HA.mat (AF F) σ J g).1 (fun i => inclR (AF F) (x 0 i)) i
    rw [e, e'] at this
    exact this.symm.trans (congrFun e' i)
  have h4 : StabHat F (L : Set (Fin M → E)) (finMat σ J g) ↔
      StabHat F (perpIn σ J L (x 0)) (finMat σ J g) := by
    have := SetLike.ext_iff.1 h3 (finPt σ J g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_left hgf, and_iff_left hgf] at this
    exact this
  refine h4.trans (stabHat_iff (P := perpIn σ J L (x 0)) B _ hN (fun z => (hL' z).trans ⟨fun h => ⟨h, k1 z⟩, fun h => h.1⟩)
    (fun y hy => k2 y hy.2) _ (finMat σ J g⁻¹) _ (finMat σ J' g'⁻¹) ?_ ?_ ?_)
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · have : ((HA.mat (AF F) σ J g).1 * B.map (inclR (AF F))).map p =
        (B.map (inclR (AF F)) * (HA.mat (AF F) σ J' g').1).map p := congrArg (fun X => Matrix.map X p) hr
    have := (Matrix.map_mul (f := p)).symm.trans (this.trans (Matrix.map_mul (f := p)))
    rw [map_snd_incl] at this
    exact this

end GlobalTheory.StabFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemIntVIffOfSplitting
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.SplitIntegers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem conj_tmul (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    Formalism.UG.sigR hc.sig R (a ⊗ₜ[F] y) = star a ⊗ₜ[F] y := rfl

omit [NumberField F] [NumberField E] [StarRing E] in
theorem algebraMap_tmul {R : Type} [CommRing R] [Algebra F R] (c : F) (y : R) :
    (algebraMap F E c) ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (algebraMap F R c * y) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

theorem exists_add_conj (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    ∃ p : R, z + Formalism.UG.sigR hc.sig R z = (1 : E) ⊗ₜ[F] p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, h⟩ := (hc.fixed (a + star a)).1 (by simp [add_comm])
    exact ⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add, TensorProduct.tmul_add, ← hp, ← hq]; ring

theorem exists_of_conj_eq (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] {z : E ⊗[F] R}
    (hz : Formalism.UG.sigR hc.sig R z = z) : ∃ p : R, (1 : E) ⊗ₜ[F] p = z := by
  obtain ⟨p, hp⟩ := exists_add_conj hc z
  rw [hz, ← two_smul F z] at hp
  refine ⟨(2⁻¹ : F) • p, ?_⟩
  rw [TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_diag (hc : CMData F E) {K : Type} [Field K] [Algebra F K]
    (φ : E ⊗[F] K ≃+* K × K) (hφ : ∀ x, φ (Formalism.UG.sigR hc.sig K x) = swapR _ (φ x)) :
    ∃ θ : K ≃+* K, ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (θ y, θ y) := by
  let f : K →+* K := ((RingHom.fst K K).comp φ.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom
  have hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y) := fun y => by
    have h := hφ ((1 : E) ⊗ₜ[F] y)
    rw [conj_tmul, star_one] at h
    have h2 := congrArg Prod.snd h
    exact Prod.ext rfl h2
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩
  obtain ⟨p, hp⟩ := exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by
    rw [hφ, φ.apply_symm_apply]; rfl))
  refine ⟨p, ?_⟩
  have := hf p
  rw [hp, φ.apply_symm_apply] at this
  exact (congrArg Prod.fst this).symm

theorem mem_of_isIntegral (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : IsIntegral ℤ x) : x ∈ v.adicCompletionIntegers F := by
  have hi : IsIntegral (v.adicCompletionIntegers F) x := hx.tower_top
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

omit [NumberField E] [StarRing E] [Algebra F E] in
theorem map_mem {S : Type} (v : HeightOneSpectrum (𝓞 F)) [FunLike S E (v.adicCompletion F)]
    [RingHomClass S E (v.adicCompletion F)] (g : S) (a : 𝓞 E) :
    g (algebraMap (𝓞 E) E a) ∈ v.adicCompletionIntegers F :=
  mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ)
    (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))

end GlobalTheory.SplitIntegers

namespace GlobalTheory

open SplitIntegers

theorem mem_intV_iff_of_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)), (∀ (θ : v.adicCompletion F ≃+* v.adicCompletion F) (x : v.adicCompletion F), θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F) → ∀ (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, φ (Formalism.UG.sigR hc.sig (v.adicCompletion F) x) = swapR _ (φ x)) → ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ hc v hθ φ hφ
  obtain ⟨θ, hd⟩ := exists_diag hc φ hφ
  have hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F :=
    fun y hy => (hθ θ.symm y).2 hy
  let ι : E →+* v.adicCompletion F × v.adicCompletion F := φ.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
  have hι : ∀ a : 𝓞 E,
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F := fun a =>
    ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩
  intro x
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · exact hι a
      · beta_reduce
        rw [hd]
        exact ⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | one => rw [map_one]; exact ⟨one_mem _, one_mem _⟩
    | add x y _ _ hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.Mass.Genus.exists_over (E := E) v
    obtain ⟨w, t, ht, hwt⟩ := hc.cmUnram.2.2 P hP
    obtain ⟨s, hs⟩ := (hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by
      rw [map_mul, map_sub, ht, star_mul, star_sub, star_star]; ring)
    have hsi : IsIntegral ℤ s := by
      have := ((w - t) * (w - t)).isIntegral_coe
      rw [← hs] at this
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this
    let s' : 𝓞 F := ⟨s, hsi⟩
    have hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t) := RingOfIntegers.ext hs
    have hsv : s' ∉ v.asIdeal := fun h => by
      rw [← hPv, Ideal.mem_comap, hs'] at h
      exact hwt ((hP.isPrime.mem_or_mem h).elim id id)
    obtain ⟨u, hu⟩ := ((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv
    have hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1 :=
      congrArg Subtype.val hu
    obtain ⟨hα, hβ⟩ := hι w
    have e1 := hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)
    rw [conj_tmul, ← ht] at e1
    have e2 := hd (algebraMap F (v.adicCompletion F) s * 1)
    rw [← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub,
      e1] at e2
    generalize hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2
    obtain ⟨α, β⟩ := W
    have e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s) := congrArg Prod.fst e2
    have e4 : θ u * ((α - β) * (α - β)) = 1 := by rw [e3, ← map_mul, hu', map_one]
    have hθu : θ u ∈ v.adicCompletionIntegers F := (hθ θ u).2 u.2
    set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef
    have hcm : c ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))
    have hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) +
        ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) := by
      apply φ.injective
      rw [map_add, map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · change (φ x).1 = (φ x).1 - c * α + c * α
        ring
      · change (φ x).2 = (φ x).1 - c * α + c * β
        rw [hcdef]
        linear_combination ((φ x).1 - (φ x).2) * e4
    rw [hx]
    refine add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩))
      (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩))
        (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QdChoiceOfHyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem qdChoice_of_explicitFormula : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → QDChoice := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 eps he he'
  obtain ⟨x0, C, hC, h⟩ := GlobalTheory.T.exists_prime_pair_box_bounds h1 h2 h3 h4 h5 h6 h7 h8 eps he he'
  refine ⟨C, x0, hC, fun x hx n hn hn' => ?_⟩
  obtain ⟨q, d, hb, hq, hr⟩ := h x hx
  exact ⟨q, d, hr n hn hn', hq, hb⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
section
namespace GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular

theorem quotientMeasures : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures :=
  ⟨GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular, GlobalTheory.T.quotientMeasure_normalised_by_haar_unique, GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula, GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula, GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left, GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space,
    GlobalTheory.T.compactSubgroup_quotient_invariant_measure⟩

end GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuouStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧ (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧ Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  first | exact @GlobalTheory.decay_integrable_periodise | exact GlobalTheory.decay_integrable_periodise | (intros; apply GlobalTheory.decay_integrable_periodise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
section
namespace GlobalTheory.StabOrbit

theorem stabTransitive : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive :=
  GlobalTheory.Proof.SelfDualStabilizer.stabTransitive_iff.1 (stabTransitive_of_lemmas GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis)

end GlobalTheory.StabOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslatesStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPairPullback_lattices_translates : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  first | exact @GlobalTheory.MomPull.pull_unitary | exact GlobalTheory.MomPull.pull_unitary | (intros; apply GlobalTheory.MomPull.pull_unitary <;> assumption)
end

