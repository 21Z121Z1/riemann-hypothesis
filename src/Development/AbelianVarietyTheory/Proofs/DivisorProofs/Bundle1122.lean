import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountUpSt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquiv
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc

theorem localTransfer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  intro p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩
  have hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q := fun q =>
    RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q
  let e' : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) hq
  let T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C := Algebra.TensorProduct.congr e' AlgEquiv.refl
  have hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c := by
    intro c
    simp [T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x) := by
    intro x
    simp [T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
  have hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : T (r ⊗ₜ x) = e r ⊗ₜ x := by
        simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rw [this, starT_tmul, starT_tmul]
      simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]
  refine ⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩
  · have := hc.map T
    rw [hT1] at this
    exact this
  · have h' := congrArg T h
    rw [hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3] at h'
    simpa using h'

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_roots_dilation_coprime_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  first | exact @GlobalTheory.DilateLevel.dilate | exact GlobalTheory.DilateLevel.dilate | (intros; apply GlobalTheory.DilateLevel.dilate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.UCls

theorem massBound_of_tamagawa : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  intro hT E _ _ _ r M h m G Λ Ψ X g x0 FF hr hM hU hSD htor hUA hdist hX
  classical
  set Cc : ℝ := ((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E with hCc
  set P0 : ℝ := (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hP0
  set R : ℝ := rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) with hR
  set K : ℝ := (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R * P0 with hK
  have hCpos : 0 < Cc := pow_pos (mul_pos (mul_pos (by positivity) (by positivity))
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r)))) _
  have hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity
  have hP0nn : 0 ≤ P0 := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hprod) _
  have hRnn : 0 ≤ R := Real.rpow_nonneg (by unfold rdE; exact Real.rpow_nonneg (by unfold dE; positivity) _) _
  have hP0le : P0 ≤ Cc := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hprod) (GlobalTheory.volumeConstant_le r hr) _
  have hKnn : 0 ≤ K := by positivity
  have hdet : ∀ i, ∀ γ ∈ (X i).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := fun i =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three E r M (X i) hM (by rw [(hX i).1]; exact (hX i).2.2.2.1)
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hV1 : ∀ i, ENNReal.ofReal Cc * muF (X i) (x0 i) (FF i) = cv i := fun i =>
    GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass E r (X i) (x0 i) (FF i) (by omega) (hdet i) (hX i).2.2.2.2.1 (hX i).2.2.2.2.2
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => GlobalTheory.T.isTA_conj_det_of_isUA_cm E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine GlobalTheory.T.unitary_frames_strong_approximation hT E r M m G Λ Ψ X g x0 _ (g i0) hr hM hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => ⟨(hX i).1, (hX i).2.1, (hX i).2.2.1, (hX i).2.2.2.1, (hX i).2.2.2.2.1⟩)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact GlobalTheory.T.equivalence_generated_torus_rel E r M G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  have hsum : ∑ i, cv i ≤ ENNReal.ofReal (h * K) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
      (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
    calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
      _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  have hmu : ∀ i, muF (X i) (x0 i) (FF i) = cv i / ENNReal.ofReal Cc := by
    intro i
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hCpos).ne' ENNReal.ofReal_ne_top]
    exact hV1 i
  calc ∑ i, muF (X i) (x0 i) (FF i) = (∑ i, cv i) * (ENNReal.ofReal Cc)⁻¹ := by
        simp only [hmu, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (h * K) * (ENNReal.ofReal Cc)⁻¹ := by gcongr
    _ = ENNReal.ofReal (h * K / Cc) := by rw [ENNReal.ofReal_div_of_pos hCpos, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (massBd E r M h) := by
        apply ENNReal.ofReal_le_ofReal
        have hA : 0 ≤ (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by positivity
        have hq : P0 / Cc ≤ 1 := (div_le_one hCpos).2 hP0le
        calc (h : ℝ) * K / Cc = ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * (P0 / Cc) := by
              rw [hK]; ring
          _ ≤ ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * 1 := mul_le_mul_of_nonneg_left hq hA
          _ ≤ 2 * (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by nlinarith
          _ = massBd E r M h := rfl

end GlobalTheory.UCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitsGiveMatrixAlgebraIso
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_units_give_matrix_algebra_iso : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  first | (exact @GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (exact GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (intros; apply GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.PlaneSkew

variable {E : Type} [Field E] [NumberField E]

def lowLat {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n₁ → E) :=
  L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))

theorem mem_lowLat {n n₁ : ℕ} {ι : Matrix (Fin n) (Fin n₁) E} {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin n₁ → E} :
    u ∈ lowLat ι L ↔ ι *ᵥ u ∈ L := Iff.rfl

def PrimAt (𝔓 : HeightOneSpectrum (𝓞 E)) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) : Prop :=
  (∀ s : E, s • x ∈ L → 𝔓.valuation E s ≤ 1) ∧ ∃ s : E, s • x ∈ L ∧ 𝔓.valuation E s = 1

end GlobalTheory.PlaneSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernel
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.JointKer

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dual_contr (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (ν : Module.Dual ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    ν (GlobalTheory.TensorFactorUnique.contr f w y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update f w ν)) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.TensorFactorUnique.contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem contr_atPl (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (L : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    GlobalTheory.TensorFactorUnique.contr f w (atPl w L y) = L (GlobalTheory.TensorFactorUnique.contr f w y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, atPl_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, GlobalTheory.TensorFactorUnique.contr_tprod,
      map_smul, Function.update_self, LinearMap.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem atPl_eq_zero_of_common (w : T) (F : Set (Module.End ℂ (V w))) (g : Module.End ℂ (V w))
    (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0) (y : ⨂[ℂ] i, V i) (hy : ∀ L ∈ F, atPl w L y = 0) :
    atPl w g y = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.TensorFactorUnique.contr f w y) = 0 := hg _ fun L hL => by rw [← contr_atPl, hy L hL, map_zero]
  have h := dual_contr f w (f w) (atPl w g y)
  rw [contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

theorem atPl_sub_one (w : T) (p : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    atPl w (p - 1) y = atPl w p y - y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, LinearMap.sub_apply, Module.End.one_apply,
      MultilinearMap.map_update_sub, Function.update_eq_self, smul_sub]
  | add a b ha hb => rw [map_add, map_add, ha, hb]; abel

theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (A : Submodule ℂ M) :
    ∃ π : Module.End ℂ M, (∀ v, π v ∈ A) ∧ ∀ v ∈ A, π v = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)
  refine ⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩
  have := congrArg (fun h => ((h ⟨v, hv⟩ : A) : M)) hg
  simpa using this

end GlobalTheory.HoweR.JointKer

namespace GlobalTheory.HoweR

open JointKer

theorem mem_tensAll_of_killed : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)),
    (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) →
    y ∈ tensAll H := by
  intro T _ _ V _ _ L H hH y hy
  choose p hpK hpid using fun w => exists_proj (H w)
  have hfix : ∀ w, atPl w (p w) y = y := by
    intro w
    have h0 := atPl_eq_zero_of_common w (L w) (p w - 1) (fun v hv => by
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v (hH w v hv), sub_self]) y (hy w)
    rw [atPl_sub_one] at h0
    exact sub_eq_zero.1 h0
  have hmap : ∀ s : Finset T,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) =
          fun w => (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hy' : PiTensorProduct.map p y = y := by
    have := hmap Finset.univ
    simpa using this
  rw [← hy']
  clear hy' hmap hfix hy
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, rfl⟩)
  | add x z hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtOfNotIsReal
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ChowHt GlobalTheory.HermTools

namespace GlobalTheory.HilbertSamuel

theorem denseRange_of_not_isReal {K : Type*} [Field K] {σ : K →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · refine absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)) hσ
    obtain ⟨r, hr⟩ := h.le (Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    exact congrArg (fun s : Subfield ℂ => (s : Set ℂ)) h

theorem frameNorm_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (fun j => c * x j) = ‖c‖ * frameNorm A x := by
  change frameNorm A (c • x) = _
  simp only [frameNorm, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Continuous (frameNorm A) := by
  unfold frameNorm Matrix.mulVec dotProduct
  fun_prop

theorem continuous_cnrm {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (h : HermFam K V)
    (σ : K →+* ℂ) (v : ι → V) : Continuous fun c => cnrm h σ c v := by
  unfold cnrm csq
  fun_prop

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_mem_span {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    {S : Set V} (hS : Submodule.span F S = ⊤) (x : V) : ∃ a : F, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 F) S := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 F)) F S x (hS.ge trivial)
  refine ⟨algebraMap (𝓞 F) F t, ?_, by rwa [algebraMap_smul]⟩
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 (nonZeroDivisors.coe_ne_zero t)

namespace Data

variable {X : Data F} {β : (F →+* ℂ) → ℝ}

theorem MulBound.of_field (h : X.MulBound β) {j : ℕ} (hj : j < X.T) (σ : F →+* ℂ) (u : Fin X.N → F) (f : X.V j)
    (g : X.V (j + 1)) (e : (g : X.Sec (j + 1)) = X.mulW j u f) :
    (X.nm (j + 1)).nrm σ g ≤ Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (u k)) * (X.nm j).nrm σ f := by
  obtain ⟨a, ha, hu⟩ := exists_smul_mem_span X.geom.alg.spans u
  obtain ⟨b, hb, hf⟩ := exists_smul_mem_span (X.full j).span f
  rw [Submodule.span_eq] at hf
  have key : (X.nm (j + 1)).nrm σ (a • b • g) ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (a * u k)) * (X.nm j).nrm σ (b • f) :=
    h j hj σ _ hu _ hf (a • b • g) (by
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, e, map_smul, map_smul, LinearMap.smul_apply,
        smul_comm])
  simp only [map_mul, frameNorm_mul, HermFam.nrm_smul_up] at key
  have ha' : 0 < ‖σ a‖ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have hb' : 0 < ‖σ b‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb)
  exact le_of_mul_le_mul_left (by linarith) (mul_pos ha' hb')

theorem MulBound.mulBoundAt_of_not_isReal (h : X.MulBound β) {σ : F →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    X.MulBoundAt σ (β σ) := fun j hj u m c f g hg => by
  have hd := denseRange_of_not_isReal hσ
  refine ((DenseRange.piMap fun _ : Fin X.N => hd).prodMap (DenseRange.piMap fun _ : Fin m => hd)).induction_on
    (p := fun z => cnrm (X.nm (j + 1)) σ (fun t => z.1 t.1 * z.2 t.2) g ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) z.1 * cnrm (X.nm j) σ z.2 f) (u, c) ?_ ?_
  · exact isClosed_le ((continuous_cnrm _ _ _).comp (by fun_prop))
      ((continuous_const.mul ((continuous_frameNorm _).comp continuous_fst)).mul
        ((continuous_cnrm _ _ _).comp continuous_snd))
  · rintro ⟨a, b⟩
    have := h.of_field hj σ a (∑ i, b i • f i) (∑ t : Fin X.N × Fin m, (a t.1 * b t.2) • g t) (by
      conv_rhs => rw [pi_eq_sum_univ' a]
      simp only [Fintype.sum_prod_type, Submodule.coe_sum, Submodule.coe_smul, hg, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _))
    simp only [← cnrm_map, map_mul] at this
    exact this

theorem MulBound.mulBoundAt [IsTotallyComplex F] (h : X.MulBound β) (σ : F →+* ℂ) : X.MulBoundAt σ (β σ) :=
  h.mulBoundAt_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)

end Data

end GlobalTheory.HilbertSamuel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem nonempty_ix_of_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 P ψ Zs hOk hin hpos
  by_contra hne
  have hfalse : ∀ x, ¬ A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id x := by
    rintro x ⟨p, hp, -⟩
    exact hne ⟨⟨p, hp⟩⟩
  have hsame := A3.fam3.sameTypes_base3 hOk P ψ hin
  have hbot : Formalism.L2.Col.eigSum (A3.fam3.RI A3.fam3.F.μ0).opAll
      (A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id) = ⊥ := by
    unfold Formalism.L2.Col.eigSum
    simp [hfalse]
  rw [hbot, BlockDat.good_part_coordinates_bot, le_bot_iff] at hsame
  unfold FamIn3.side3 DefFam3.side3 DefSide.Pos at hpos
  simp only [BlockDat.dZ, subDim] at hpos
  rw [hsame] at hpos
  simp at hpos

end GlobalTheory.Div
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasFormStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_equivariant_pairing_has_form : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 → (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) → GlobalTheory.RealLift.HasForm P Q R S x := by
  first | exact @GlobalTheory.FockSplit.hasForm_of_pairing | exact GlobalTheory.FockSplit.hasForm_of_pairing | (intros; apply GlobalTheory.FockSplit.hasForm_of_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyPeriodLatticePropertiesHold
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem periodLattices : PeriodLattices := by
  intro D X s cc δ B χ cD _hX hok _h1 _h2 hcc hδ _hχ _hdg _hY a b S ha hb hconj hU
  exact ⟨KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, hU, aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumThetaStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (g : ℕ) (X : Data D.host.E W.rank) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin W.rank) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (he : Even V.rank), V.gram = 1 → IsMod W rfl X → IsSympl X bas → ∃ (X' : Data D.host.E W.rank) (m : GlobalTheory.Ker.Match V W X') (hq' : X'.p0 + X.p0 = W.rank) (hq : X.p0 + X'.p0 = W.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin W.rank) (hs : IsSympl X' bas'), X'.Λ = X.Λ ∧ (∀ a, (bas' a : Fin W.rank → D.host.E) = bas a) ∧ (∀ u v, EF X' u v = EF X u v) ∧ (∀ (y : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (φ : TF V.rank g), heisG X' bas' y φ = heisG X bas y φ) ∧ (∀ j (a : Fin W.rank) (k : Fin X'.p0 ⊕ Fin X.p0), (idx j).2 = rowIdx hq k → ((idx' j).2 : ℕ) = Sum.elim (fun i : Fin X'.p0 => (i : ℕ)) (fun i : Fin X.p0 => X'.p0 + (i : ℕ)) k) ∧ (∀ j, (idx' j).1.1 = ComplexEmbedding.conjugate (idx j).1.1) ∧ ∀ x : Frame X.Ψ W.rank, IsONFr X x → (∃ B, IsBasOf W rfl X hq x B) ∧ ∀ B, IsBasOf W rfl X hq x B → let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs, he⟩; C.IsB B ∧ IsInvOf W rfl X x (C.sB B) ∧ (∀ s, IsInvOf W rfl X x s → s = C.sB B) ∧ (∀ w, C.zOf (C.xB B) w = zOf θ V W rfl X idx x w) ∧ (∀ v, pv X' idx' (C.xB B) v = pv X idx x v) ∧ (∀ z z', hx X' bas' idx' (C.xB B) z z' = hx X bas idx x z z') ∧ (∀ φ : TF V.rank g, thA X' bas' idx' φ (C.xB B) = thA X bas idx φ x) ∧ (∀ u : GA D W, IsONFr X (frMove θ W rfl X u x) ∧ IsBasOf W rfl X hq (frMove θ W rfl X u x) (C.mvB u B)) ∧ ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ → ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB B) φ) := by
  first | exact @GlobalTheory.AdTh.reads_iff_eq_th | exact GlobalTheory.AdTh.reads_iff_eq_th | (intros; apply GlobalTheory.AdTh.reads_iff_eq_th <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixingStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_support_finite_of_finite_fixing : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  first | (exact @GlobalTheory.CxUnfold.support_cxF_finite) | (exact GlobalTheory.CxUnfold.support_cxF_finite) | (intros; apply GlobalTheory.CxUnfold.support_cxF_finite <;> assumption)
end

