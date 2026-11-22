import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
section
namespace GlobalTheory.UnitaryChar

section Mat

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

theorem root {S A : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_std {S U : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix (Fin n) (Fin n) ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem polar {G s u : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.IndefR.Datum.IsCartanInv G s) (hu : uᴴ * G * u = G) :
    ∃ k q : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G ∧ s * k = k * s ∧ qᴴ * G * q = G ∧ s * q * s * q = 1 ∧
      u = k * q * q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG : Gᴴ = G := by
    have e : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul, h3.isHermitian.eq]
    have e1 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← Matrix.one_mul Gᴴ, ← e1, Matrix.mul_assoc, e, ← Matrix.mul_assoc, h2]
  obtain ⟨B, hB, hBB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ = B ∧ B * B = G * s :=
    ⟨CFC.sqrt (G * s), (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ h3.posSemidef.nonneg⟩
  have hd : IsUnit B.det := by
    have : IsUnit (B * B).det := by rw [hBB]; exact (Matrix.isUnit_iff_isUnit_det _).1 h3.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨C, hC, i1, i2⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ = C ∧ B * C = 1 ∧ C * B = 1 :=
    ⟨B⁻¹, by rw [Matrix.conjTranspose_nonsing_inv, hB], Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩
  have j1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, B * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, C * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  obtain ⟨S, hs, hGS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, s = C * S * B ∧ G = B * S * B :=
    ⟨B * s * C, by simp only [Matrix.mul_assoc, j2, i2, Matrix.mul_one], by
      simp only [Matrix.mul_assoc, i2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hBB, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  have hS : S = C * G * C := by rw [hGS]; simp only [Matrix.mul_assoc, j2, i1, Matrix.mul_one]
  have s1 : S * S = 1 := by
    have := congrArg (fun X => B * X * C) h1
    simpa only [hs, Matrix.mul_assoc, j1, i1, Matrix.mul_one] using this
  have s2 : Sᴴ = S := by
    rw [hS]; simp only [Matrix.conjTranspose_mul, hC, hG, Matrix.mul_assoc]
  have tr : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * S * X = S → (C * X * B)ᴴ * G * (C * X * B) = G := fun X hX => by
    calc _ = B * (Xᴴ * S * X) * B := by
          rw [hGS]; simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc, j1, j2]
      _ = G := by rw [hX, hGS]
  obtain ⟨K, Q, k1, k2, q1, q2, e⟩ := polar_std (U := B * u * C) s1 s2 (by
    calc _ = C * (uᴴ * (B * S * B) * u) * C := by
          simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc]
      _ = S := by rw [← hGS, hu, ← hS])
  refine ⟨C * K * B, C * Q * B, tr K k1, ?_, tr Q q1, ?_, ?_⟩
  · have := congrArg (fun X => C * X * B) k2
    simpa only [hs, Matrix.mul_assoc, j1] using this
  · have := congrArg (fun X => C * X * B) q2
    simpa only [hs, Matrix.mul_assoc, j1, Matrix.one_mul, i2] using this
  · have := congrArg (fun X => C * X * B) e
    simpa only [Matrix.mul_assoc, j1, j2, i2, Matrix.mul_one] using this

end Mat

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem compAt_mt_mul {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) (g g' : GA D W) :
    compAt θ τ (Formalism.L2.Theta.mt W (g * g')) =
      compAt θ τ (Formalism.L2.Theta.mt W g) * compAt θ τ (Formalism.L2.Theta.mt W g') :=
  Matrix.map_mul (L := Formalism.L2.Theta.mt W g) (M := Formalism.L2.Theta.mt W g') (f := (θ τ).comp (infPart D))

theorem compAt_mt_one {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 :=
  Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem ext_real {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g g' : GA D W} (hg : g ∈ GinfC W)
    (hg' : g' ∈ GinfC W) (h : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = compAt θ τ (Formalism.L2.Theta.mt W g')) :
    g = g' := by
  refine mul_inv_eq_one.1 ((GlobalTheory.UnitarySplit.real_finite_split D W).2.2.1 _ (mul_mem hg (inv_mem hg'))
    ((GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun τ => ?_))
  show compAt θ τ (Formalism.L2.Theta.mt W (g * g'⁻¹)) = 1
  rw [compAt_mt_mul, h, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]

theorem char_eq_one : ∀ (D : D7) (θ : InfFam D) (W : HSp D), IsInfFam θ → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ c : GA D W → ℂ, (∀ u ∈ GinfC W, ∀ u' ∈ GinfC W, c (u * u') = c u * c u') → (∀ u ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W u) = compAt θ τ (Formalism.L2.Theta.mt W u) * s τ) → c u = 1) → ∀ u ∈ GinfC W, c u = 1 := by
  intro D θ W hθ s hs c hm hK u hu
  have gl : ∀ x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, (x τ)ᴴ * gramAt D W τ * x τ = gramAt D W τ) →
      ∃ g ∈ GinfC W, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = x τ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ W).2
  choose k q k1 k2 q1 q2 e using fun τ => polar (u := compAt θ τ (Formalism.L2.Theta.mt W u)) (hs τ)
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u τ)
  obtain ⟨k', hk, ek⟩ := gl k k1
  obtain ⟨q', hq, eq⟩ := gl q q1
  obtain ⟨σ, hσ, eσ⟩ := gl s fun τ => (hs τ).2.1
  have ck : c k' = 1 := hK _ hk fun τ => by rw [ek, k2]
  have cσ : c σ = 1 := hK _ hσ fun τ => by rw [eσ]
  have c1 : c 1 = 1 := hK _ (one_mem _) fun τ => by rw [compAt_mt_one, Matrix.mul_one, Matrix.one_mul]
  have e1 : u = k' * q' * q' := ext_real hθ W hu (mul_mem (mul_mem hk hq) hq) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, ek, eq, e]
  have e2 : σ * q' * σ * q' = 1 := ext_real hθ W (mul_mem (mul_mem (mul_mem hσ hq) hσ) hq) (one_mem _) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, compAt_mt_mul, eσ, eq, q2, compAt_mt_one]
  rw [← e2, hm _ (mul_mem (mul_mem hσ hq) hσ) _ hq, hm _ (mul_mem hσ hq) _ hσ, hm _ hσ _ hq, cσ, one_mul,
    mul_one] at c1
  rw [e1, hm _ (mul_mem hk hq) _ hq, hm _ hk _ hq, ck, one_mul, c1]

end GlobalTheory.UnitaryChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinGen

open GlobalTheory.LatVac GlobalTheory.LatFinMod

theorem pair_smul_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (α : Af F) (x : E) :
    algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α) * (pairA F 0 1 ⊗ₜ[F] x) = pairA F 0 α ⊗ₜ[F] x := by
  have hp : pairA F 0 α * pairA F 0 1 = pairA F 0 α := Prod.ext (mul_zero _) (mul_one _)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact congrArg (· ⊗ₜ[F] x) hp

theorem smul_finTens_one {D : D7} {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • finTens 1 M = finTens α M :=
  Matrix.ext fun i j => pair_smul_tmul α (M i j)

theorem latO_finitely_generated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  intro D S T ΛS ΛT hS hT
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS.1.fg
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT.1.fg
  refine ⟨finTens 1 '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)),
    ((hA.prod (hB.prod hC)).image _).image _, ?_, fun U hU u hu => ?_⟩
  · rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨1, fun v => ?_, fun v hv => absurd trivial hv,
      a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    rw [map_one]; exact one_mem _
  · refine (AddSubgroup.closure_le U).2 ?_ hu
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
      (AddMonoidHom.mk' (finTens α) (finTens_add α)).toIntLinearMap
    have hle : Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) ≤
        U.toIntSubmodule.comap φ := by
      refine Submodule.span_le.2 fun M hM => ?_
      have := hU α hα _ ⟨M, hM, rfl⟩
      rw [smul_finTens_one] at this
      exact this
    exact hle (genMap_mem_span S T (hA2 _ ha) (hB2 _ hs) (hC2 _ ht))

end GlobalTheory.LatFinGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLevel

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_nsmul_smul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n)))
    (y : Mx D m n) : ∃ N : ℕ, 0 < N ∧ ∀ α ∈ intAf D.host.F,
      N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) ∈ U := by
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 α :=
    continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, fun α hα => ?_⟩
  have h1 : φ (N • α) ∈ U := h α hα
  have h2 : φ (N • α) = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • α) = N • pairA D.host.F 0 α :=
      Prod.ext (show (0 : Ainf D.host.F) = N • 0 by rw [smul_zero]) rfl
    show pairA D.host.F 0 (N • α) • y i j = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * y i j)
    rw [e1, smul_assoc, Algebra.smul_def (pairA D.host.F 0 α)]
  rwa [h2] at h1

def actHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by
    unfold actO
    rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [actO, Matrix.mul_apply]
  refine continuous_finset_sum _ fun k _ => Continuous.mul (continuous_finset_sum _ fun l _ =>
    continuous_const.mul ?_) continuous_const
  exact (continuous_apply k).comp (continuous_apply l)

theorem actO_map_inf (S T : HSp D) (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

def finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) :=
  (L.map (finPart D).toAddMonoidHom.mapMatrix).comap (finPart D).toAddMonoidHom.mapMatrix

theorem mem_finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) (x : Mx D m n) :
    x ∈ finSat L ↔ ∃ l ∈ L, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 := by
  have key : ∀ l : Mx D m n, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 ↔
      (finPart D).toAddMonoidHom.mapMatrix l = (finPart D).toAddMonoidHom.mapMatrix x := by
    intro l
    rw [one_smul, eq_comm (b := (finPart D).toAddMonoidHom.mapMatrix x), ← sub_eq_zero (a := (finPart D).toAddMonoidHom.mapMatrix x), ← map_sub]
    rfl
  simp only [key]
  rfl

theorem level_of_generators : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT ⟨G, hG, _, hgen⟩
  have h1 : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        N • u ∈ U := by
    intro U hU
    choose M hM hMU using fun y : WO S T => exists_nsmul_smul_mem U hU y
    refine ⟨∏ y ∈ hG.toFinset, M y, Finset.prod_pos fun y _ => hM y, ?_⟩
    refine hgen (U.comap (nsmulAddMonoidHom (∏ y ∈ hG.toFinset, M y))) fun α hα u hu => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem M (hG.mem_toFinset.2 hu)
    show (∏ y ∈ hG.toFinset, M y) • _ ∈ U
    rw [hc, mul_comm, mul_smul]
    exact U.nsmul_mem (hMU u α hα) c
  refine ⟨h1, fun g h => ?_⟩
  have hop : IsOpen (finSat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) : Set (WO S T)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos using 1
    exact Set.ext fun x => mem_finSat _ x
  obtain ⟨N, hN, hNU⟩ := h1 ((finSat _).comap (actHom S T g h)) (hop.preimage (continuous_actO S T g h))
  refine ⟨N, hN, fun u hu => ?_⟩
  have h2 : actHom S T g h (N • u) ∈ finSat _ := hNU u hu
  obtain ⟨l, hl, hl0⟩ := (mem_finSat _ _).1 h2
  have h3 : (actHom S T g h (N • u)).map (infPart D) = 0 :=
    actO_map_inf S T g h (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  have h4 := latO_fin hl
  have h5 : actHom S T g h (N • u) = l := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · exact (congrFun (congrFun h3 i) j).trans (congrFun (congrFun h4 i) j).symm
    · have h6 : finPart D (actHom S T g h (N • u) i j - (1 : ℕ) • l i j) = 0 := congrFun (congrFun hl0 i) j
      rwa [one_smul, RingHom.map_sub, sub_eq_zero] at h6
  rw [map_nsmul] at h5
  exact h5 ▸ hl

end GlobalTheory.LatLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfComplexBaseChange
section
noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isHolTo_congr_on {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : ∀ b ∈ B, y b = y' b) : IsHolTo B y ↔ IsHolTo B y' := by
  have hs : ∀ U : X.Opens, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} := fun U =>
    Set.ext fun b => ⟨fun ⟨hb, h'⟩ => ⟨hb, by rw [← h b hb]; exact h'⟩, fun ⟨hb, h'⟩ => ⟨hb, by rw [h b hb]; exact h'⟩⟩
  constructor
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [← hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩

theorem unif_of_isBC : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R]
    (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g),
    IsBC F' F σ → Nonempty (Unif F' (RingHom.id ℂ) ρ N C) → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C F' hbc hU
  obtain ⟨U'⟩ := hU
  obtain ⟨f, φ, hpb, hgp, hact, hL, heta⟩ := hbc
  have hw : φ ≫ F.A.hom = F'.A.hom ≫ f := hgp.1.w
  have hsq : f ≫ F.s = F'.s ≫ spMap σ := hpb.w
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hbase : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' h
    rw [Category.assoc, hsq, ← Category.assoc, h, hid, Category.id_comp]
  have hinj : ∀ y₁ y₂ : Sp ℂ ⟶ F'.X, y₁ ≫ F'.s = spMap (RingHom.id ℂ) → y₂ ≫ F'.s = spMap (RingHom.id ℂ) →
      y₁ ≫ f = y₂ ≫ f → y₁ = y₂ := fun y₁ y₂ h₁ h₂ h => hpb.hom_ext h (by rw [h₁, h₂])
  let exF : ∀ i P, (Fin g → ℂ) → (Over.mk (U'.u i P ≫ f) ⟶ F.A) := fun i P z =>
    Over.homMk ((U'.ex i P z).left ≫ φ) (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
  refine ⟨{
      n := U'.n, Di := U'.Di, t := U'.t, mem := U'.mem, ne := U'.ne, all := U'.all, distinct := U'.distinct
      u := fun i P => U'.u i P ≫ f, ex := exF, unif := ?_, onto := ?_, disj := ?_, fibre := ?_, hol := ?_, lift := ?_ }⟩
  · intro i P hP
    have h := U'.unif i P hP
    obtain ⟨e, he, hee⟩ := (GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ hgp hact hL heta (U'.Di i) (U'.t i) P
      (U'.u i P) h.1 (hbase _ h.1)).1 _ h
    have : e = exF i P := funext fun z => Over.OverMorphism.ext (by rw [hee z]; rfl)
    rw [← this]
    exact he
  · intro y hy
    obtain ⟨i, P, hP, hu⟩ := U'.onto (hpb.lift y (spMap (RingHom.id ℂ)) (by rw [hy, hid, Category.id_comp]))
      (IsPullback.lift_snd _ _ _ _)
    refine ⟨i, P, hP, ?_⟩
    show U'.u i P ≫ f = y
    rw [hu, IsPullback.lift_fst]
  · intro i j P P' hP hP' h
    exact U'.disj i j P P' hP hP' (hinj _ _ (U'.unif i P hP).1 (U'.unif j P' hP').1 h)
  · intro i P P' hP hP'
    refine Iff.trans ⟨fun h => hinj _ _ (U'.unif i P hP).1 (U'.unif i P' hP').1 h, fun h => ?_⟩ (U'.fibre i P P' hP hP')
    show U'.u i P ≫ f = U'.u i P' ≫ f
    rw [h]
  · intro i m B P hB hP
    obtain ⟨h1, h2⟩ := U'.hol i m B P hB hP
    refine ⟨(GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb (Fin m → ℂ) B (fun b => U'.u i (P b))
      (fun b hb => (U'.unif i (P b) (hP.1 b hb)).1)).1 h1, ?_⟩
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 φ
  · intro m B y hB hy hhol b₀ hb₀
    classical
    let y' : (Fin m → ℂ) → (Sp ℂ ⟶ F'.X) := fun b =>
      if h : y b ≫ F.s = spMap σ then hpb.lift (y b) (spMap (RingHom.id ℂ)) (by rw [h, hid, Category.id_comp])
      else hpb.lift (y b₀) (spMap (RingHom.id ℂ)) (by rw [hy b₀ hb₀, hid, Category.id_comp])
    have hy'1 : ∀ b ∈ B, y' b ≫ F'.s = spMap (RingHom.id ℂ) := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_snd _ _ _ _
    have hy'2 : ∀ b ∈ B, y' b ≫ f = y b := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_fst _ _ _ _
    have hh : IsHolTo B y' := (GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb _ B y' hy'1).2
      ((isHolTo_congr_on fun b hb => (hy'2 b hb).symm).1 hhol)
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := U'.lift m B y' hB hy'1 hh b₀ hb₀
    refine ⟨B', i, P, hB', hb', hsub, hP, fun b hb => ?_⟩
    show U'.u i (P b) ≫ f = y b
    rw [hu b hb, hy'2 b (hsub hb)]

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_thV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Continuous (thV ψ Φ) := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  have hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N =>
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    intro ξ
    refine Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))
    refine Continuous.add ?_ (continuous_const.mul ?_)
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    funext w
    simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
    rfl
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
  obtain ⟨c, hcs, hc0, hcb⟩ := hk (Prod.fst '' ω) (hωc.image continuous_fst)
  have hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_
    rw [norm_mul, hψn, one_mul]
    by_cases hmem : fin (rat ξ + w.1) ∈ K
    · have h1 := hcb ξ w.1 ⟨w, hw, rfl⟩ hmem
      have h2 := hC (rat ξ + w.1)
      calc ‖Φ (rat ξ + w.1)‖ = ‖Φ (rat ξ + w.1)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + w.1)‖ * (c ξ * (1 + sz (rat ξ + w.1)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + w.1)‖ * (1 + sz (rat ξ + w.1)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  exact hon.continuousAt hωn

end GlobalTheory.ThetaTransform
end

