import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfolding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
  GlobalTheory.PairStep.logCanonicalCut_of_step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeIsotropicFlagStabilizerNotRaiseWeightStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositeIsotropicFlagStabilizer_not_raise_weight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  first | exact @GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag | exact GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag | (intros; apply GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  first | exact @GlobalTheory.Unfold.twOrb_unfold | exact GlobalTheory.Unfold.twOrb_unfold | (intros; apply GlobalTheory.Unfold.twOrb_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermPointSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_point_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  first | (exact @GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (exact GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (intros; apply GlobalTheory.LKMid.Pair.term_one_eq_pointSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvector
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.LineGlue

theorem map_mul_eq_of_local {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (U : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin 1) R) (P : Matrix (Fin 1) (Fin n) R)
    (hPX : P * X = 1) (β : Matrix (Fin 1) (Fin 1) S) (h : U.map φ * X.map φ = X.map φ * β) :
    (U * X).map φ = (X * (P * U * X)).map φ := by
  have hβ : (P * U * X).map φ = β := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hPX,
      Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul]
  rw [Matrix.map_mul, h, ← hβ, ← Matrix.map_mul]

end GlobalTheory.LineGlue

theorem GlobalTheory.LineGlue.exists_idele_smul_of_local_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  intro F E _ _ _ _ _ σ n J x pL hpx q hInf hFin
  set U := matHom (AF F) σ J q with hU
  set X := adMat F x with hX
  set P := pL.map (inclR (F := F) (AF F)) with hP
  have hPX : P * X = 1 := by
    rw [hP, hX, adMat, ← Matrix.map_mul, hpx, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinclFin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      x.map (inclR (F := F) (Fv F v)) = X.map (compFin F E v) := by
    intro v
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compFin, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hinclInf : ∀ w : InfinitePlace F,
      x.map (inclR (F := F) w.Completion) = X.map (compInf F E w) := by
    intro w
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compInf, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hMX : U.1 * X = X * (P * U.1 * X) := by
    ext i j
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun v => ?_)
    · obtain ⟨β, hβ⟩ := hInf w
      rw [matHom_projArch, hinclInf] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compInf F E w) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
    · obtain ⟨β, hβ⟩ := hFin v
      rw [matHom_proj, hinclFin] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compFin F E v) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
  obtain ⟨c', hc'⟩ : ∃ c' : AF F ⊗[F] E, c' * (P * U.1 * X) 0 0 = 1 := by
    refine ⟨(P * (U⁻¹).1 * X) 0 0, ?_⟩
    have h1 : X = (U⁻¹).1 * X * (P * U.1 * X) := by
      rw [Matrix.mul_assoc, ← hMX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h2 : P * (U⁻¹).1 * X * (P * U.1 * X) = 1 := by
      rw [show P * (U⁻¹).1 * X * (P * U.1 * X) = P * ((U⁻¹).1 * X * (P * U.1 * X)) by
        simp only [Matrix.mul_assoc], ← h1, hPX]
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using this
  refine ⟨Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hc'), ?_⟩
  rw [hMX]
  ext i j
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc : ∀ {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)), IsCompact K → (∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poinVol | exact GlobalTheory.GoodTop.integrableOn_poinVol | (intros; apply GlobalTheory.GoodTop.integrableOn_poinVol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecedesOfSegDualPrecedes
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocLanglands

theorem precedes_of_segDual_precedes :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ D : IrrGL k → IrrGL k, (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) →
      (∀ (x : IrrGL k) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) →
      (∀ x, (D x).1 = x.1) → ∀ Δ Γ Δ' Γ' : Segment k, SegDual Δ Δ' → SegDual Γ Γ' → Γ'.Precedes Δ' → Δ.Precedes Γ := by
  intro k _ _ _ _ D hD hDD hnu _ _ Δ Γ Δ' Γ' ⟨l1, d1⟩ ⟨l2, d2⟩ H
  obtain ⟨j, h0, h1, h2, e⟩ := Segment.precedes_iff.1 H
  rw [(hD _ _).1 d1, (hD _ _).1 d2] at e
  have e' := congrArg D e
  rw [hnu (D _), hDD, hDD, IrrGL.nu_nu] at e'
  rw [l1] at h2
  rw [l2] at h1 h2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j + Δ.len = Γ.len + i := ⟨j + Δ.len - Γ.len, by omega⟩
  refine Segment.precedes_iff.2 ⟨i, by omega, by omega, by omega, ?_⟩
  have hc : (j : ℂ) + Δ.len = Γ.len + i := by exact_mod_cast hi
  have e2 := congrArg (fun x => IrrGL.nu x (-((Γ.len : ℂ) - 1 + -(j : ℂ)))) e'
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at e2
  rw [← e2]
  congr 1
  linear_combination hc

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.PlacingProd

theorem multiProd_placing_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  intro k _ _ _ _ h n d e e' X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin n) (fun a => Fin (d a)) e e' _).1 _

end GlobalTheory.PlacingProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectioStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectionFormulaAndChernDegree_of_heightProjection : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ArDegree := by
  first | exact @GlobalTheory.Published.arDegree_of_heightProjection | exact GlobalTheory.Published.arDegree_of_heightProjection | (intros; apply GlobalTheory.Published.arDegree_of_heightProjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTriStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  first | exact @GlobalTheory.EtaInfSign.quadChar_eq_infSign | exact GlobalTheory.EtaInfSign.quadChar_eq_infSign | (intros; apply GlobalTheory.EtaInfSign.quadChar_eq_infSign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0
section
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.Adelic.LinSys

theorem finrank_quotient_piece_le_sections (k : Type) [Field k] (S : LinSys k) (hS : S.IsVariety)
    (m : ℕ) : Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  classical
  let : Module k (lbPow S.L m).Sec := Module.compHom (lbPow S.L m).Sec (algebraMap k Γ(S.Y, ⊤))
  have : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec :=
    ⟨fun a b s => by
      show (a • b) • s = algebraMap k Γ(S.Y, ⊤) a • (b • s)
      rw [Algebra.smul_def, mul_smul]⟩
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) (lbPow S.L m)) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj (isLB_lbPow S.isLB m)
  have : Module.Finite k (lbPow S.L m).Sec :=
    Module.Finite.equiv ((cohZeroTwistEquiv (lbPow S.L m)).restrictScalars k)
  rw [lineBundleGlobalSectionsDim_eq_finrank]
  let V := homogeneousSubmodule (Fin S.N) k m

  let φ : V →ₗ[k] (lbPow S.L m).Sec :=
    { toFun := fun g => S.form g.2
      map_add' := fun g h => (ProjCoh.formSecAdd k S.b (m : ℤ)).map_add
        ⟨g.1, mem_polyGrading_natCast.2 g.2⟩ ⟨h.1, mem_polyGrading_natCast.2 h.2⟩
      map_smul' := fun c g => ProjCoh.formSec_smul k S.b c (mem_polyGrading_natCast.2 g.2) _ }

  let f : V →ₗ[k] MvPolynomial (Fin S.N) k ⧸ S.imageIdeal :=
    (Ideal.Quotient.mkₐ k S.imageIdeal).toLinearMap ∘ₗ V.subtype
  have hker : LinearMap.ker f = LinearMap.ker φ := by
    ext g
    simp only [LinearMap.mem_ker]
    change Ideal.Quotient.mk S.imageIdeal g.1 = 0 ↔ S.form g.2 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact S.mem_imageIdeal_iff g.2
  have hrange : quotPiece S.imageIdeal (m : ℤ) = LinearMap.range f := by
    rw [quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, ← f.quotKerEquivRange.finrank_eq, (Submodule.quotEquivOfEq _ _ hker).finrank_eq,
    φ.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_le _

end GlobalTheory.Adelic.LinSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIsRatOf
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.LatMove

theorem rational_matrix_isRatOf {D : D7} (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) (τ : D.host.E →+* ℂ)
    (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (δ₁ : GL (Fin V.rank) D.host.E) (h₁ : archM V θ δ = δ₁.1.map τ) : GlobalTheory.Ker.IsRatOf V δ₁ δ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  ext i j
  have h₀ : archM V θ δ i j = τ (δ₀.1 i j) := by
    change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    exact hθ.1 _
  have e : δ₀.1 i j = δ₁.1 i j := τ.injective (by rw [← h₀, h₁]; rfl)
  exact (he' i j).trans (congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) e)

theorem kappa_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X X' : Data E r) (τ : E →+* ℂ)
    (h : τ ∈ X.Ψ) (h' : τ ∈ X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  have s1 : (τ X.κ0).im < 0 := X.κ0_sign ⟨τ, h⟩
  have s2 : (τ X'.κ0).im < 0 := X'.κ0_sign ⟨τ, h'⟩
  rcases X.κ0_xi with e | e <;> rcases X'.κ0_xi with e' | e'
  · rw [e, e', hξ]
  · rw [e, hξ] at s1
    rw [e', map_neg, Complex.neg_im] at s2
    linarith
  · rw [e, hξ, map_neg, Complex.neg_im] at s1
    rw [e'] at s2
    linarith
  · rw [e, e', hξ]

theorem flip_congr {A : Type} [AddCommGroup A] {a b y : A} {N : ℕ} (h : a - b = N • y) : b = a + N • (-y) := by
  rw [smul_neg, ← h]
  abel

set_option maxHeartbeats 1000000 in

theorem lattice_move : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), GeoSet W U dict x₀ → LatEmb W ι → ∀ d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U, d.Is W rfl dict ι x₀ → ∀ (κ : GA D W) (lev : Dw.La →ₗ[𝓞 D.host.E] Dw.La), GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W κ → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees W ι l.M (Mfr l) κ lev → ∀ h γ γ' : GA D W, d.At W rfl dict ι x₀ h γ → d.At W rfl dict ι x₀ (h * κ) γ' → ∃ (ga : GL (Fin W.rank) D.host.E) (hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1)), GlobalTheory.Ker.IsRatOf W ga (γ' * γ⁻¹) ∧ IsUn (U.X (dict (h * κ)).1) ga ∧ mapL ga (U.X (dict h).1).Λ = (U.X (dict (h * κ)).1).Λ ∧ lact ga (castFr hs.psi (dict h).2) = (dict (h * κ)).2 ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ (U.X (dict (h * κ)).1).Λ, (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) = (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E) + l.M • u := by
  intro D H Dw l Xo c σ W U dict ι x₀ hG _ d hd κ lev hκ hlev h γ γ' hat hat'
  obtain ⟨-, hU, -, -, hW, -⟩ := hG
  obtain ⟨⟨hγ, hΛ, hm⟩, hfr⟩ := hat
  obtain ⟨⟨hγ', hΛ', hm'⟩, hfr'⟩ := hat'
  have hδ : γ' * γ⁻¹ ∈ GQ W := mul_mem hγ' (inv_mem hγ)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W _ hδ
  have hprod : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ) := by group
  have hκ1 : latGHat W κ = latGHat W 1 := by
    unfold latGHat
    rw [hκ.2, (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.stabLat_one W).2]
  have hpsi : ∀ k k', (U.X k).Ψ = (U.X k').Ψ := fun k k' =>
    Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ (U.X (dict h).1).Ψ := by
    by_cases h0 : D.host.φ₀ ∈ (U.X (dict h).1).Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt ((U.X (dict h).1).cmType _).2 h0)⟩
  have hξ : (U.X (dict h).1).ξ0 = (U.X (dict (h * κ)).1).ξ0 := (hW _).2.trans (hW _).2.symm
  have hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1) :=
    ⟨hpsi _ _, (hW _).1.trans (hW _).1.symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm, hξ,
      kappa_eq _ _ τ₀ hτ₀ (hpsi _ _ ▸ hτ₀) hξ⟩
  obtain ⟨ht1, ht2⟩ := GlobalTheory.ShortMoveIso.transport (finHom W) (latGHat W)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D W g).2) l.M (γ' * γ⁻¹) (γ * h) κ hκ1
  rw [hprod] at ht1 ht2
  have hmem : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ finVec W v ∈ latGHat W (γ * h) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ (U.X (dict (h * κ)).1).Λ ↔ finVec W v ∈ latGHat W (γ' * (h * κ)) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ δ.1 *ᵥ v ∈ (U.X (dict (h * κ)).1).Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hG' : (U.X (dict (h * κ)).1).Gm = -W.gram.transpose := (hW _).1
  refine ⟨δ, hs, rational_matrix_isRatOf W _ hδ τ₀ _ (hd.1 _ ⟨τ₀, hτ₀⟩) δ (hδa _ _ (hd.1 _ ⟨τ₀, hτ₀⟩)),
    fun u v => by rw [hG']; exact hδu u v, ?_, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
  · funext τ
    have hτ : τ.1 ∈ (U.X (dict h).1).Ψ := by rw [hs.psi]; exact τ.2
    have e1 := hfr ⟨τ.1, hτ⟩
    have e2 := hfr' τ
    have hth := hd.1 _ τ
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hd.1 _ ⟨τ.1, hτ⟩) hth] at e1
    have hmul : ∀ a b : GA D W, archM W (d.th _ τ) (a * b) = archM W (d.th _ τ) a * archM W (d.th _ τ) b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM W (d.th _ τ) κ = 1 := by
      rw [archM, show infHom W κ = 1 from hκ.1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hprod, hmul, hmul, hone, Matrix.mul_one, hδa _ _ hth] at e2
    change δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hτ⟩ = mat (dict (h * κ)).2 τ
    rw [e1, e2, ← Matrix.mul_assoc]
    rfl
  · obtain ⟨y, hy, ey⟩ := hlev a ha
    obtain ⟨z, hz, e⟩ := ht2 (finVec W (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E))
      (finVec W (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) _ _
      ⟨-y, neg_mem hy, flip_congr ey⟩
      (hm _ (GlobalTheory.ShortMoveIso.map_mem_half _ lev a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0
      (δ.1 *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) -
        (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem' w).2 (hw ▸ hz), sub_eq_iff_eq_add'.1 e'⟩

end GlobalTheory.FrameEquiv.LatMove
end

