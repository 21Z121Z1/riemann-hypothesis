import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectorsStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  first | exact @GlobalTheory.TypeSum.CasBasis.casimir_scalar | exact GlobalTheory.TypeSum.CasBasis.casimir_scalar | (intros; apply GlobalTheory.TypeSum.CasBasis.casimir_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNormStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd c : ℝ), FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd → PtIn S Tn G c Gc PH Prw Pet nus → ∃ G' : GlobalFamilyData (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka wL wF, FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' Gc PH Prw Pet Pd ∧ PtIn (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' c Gc PH Prw Pet nus := by
  first | exact @GlobalTheory.NormMove.exists_famIn_ptIn | exact GlobalTheory.NormMove.exists_famIn_ptIn | (intros; apply GlobalTheory.NormMove.exists_famIn_ptIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety

theorem fixed_baseChange {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (c : E →ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (y : R ⊗[F] E)
    (hy : Algebra.TensorProduct.map (AlgHom.id F R) c y = y) : ∃ a : R, y = a ⊗ₜ 1 := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + Algebra.TensorProduct.map (AlgHom.id F R) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add, hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.tmul_add, ht,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [← TensorProduct.smul_tmul', ← ht, hy, ← two_smul F y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem

theorem fixed_conj (D : D7) (x : D.host.E) (hx : cF D x = x) : ∃ t : D.host.F, x = algebraMap D.host.F D.host.E t := by
  have : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hcard : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, D.sp.cm.deg2]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : D.host.E ≃ₐ[D.host.F] D.host.E)).1 hcard
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := D.host.F) x).2 fun f => by
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [hg f hf, ← hg _ (conj_ne_one D), hx]
  exact ⟨t, ht.symm⟩

theorem coe_cjFin (D : D7) (y : (AfE D)ˣ) : ((cjFin D y : (AfE D)ˣ) : AfE D) = barF D (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun x => (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  unfold cjFin barF
  rw [h]
  rfl

theorem finiteIdeles_normOne_eq_div_conj_with_congruence : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  intro D
  have hcc : ∀ x, cF D (cF D x) = x := fun x => star_star x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun p N x hp h2 hpN _ hx hc => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.UCls.NormOne.finiteAdele_quadratic_exists_unit_eq_mul_sg (cF D) hcc (fixed_conj D) (conj_ne_one D) (x : AfE D) hx
    refine ⟨y, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hy.symm)
  · exact fixed_baseChange (Af D.host.F) (cF D : D.host.E →ₐ[D.host.F] D.host.E) hcc (fixed_conj D) _
      ((coe_cjFin D y).symm.trans (congrArg Units.val hy))
  · obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨k, rfl⟩ := hpN
    obtain ⟨y, y', hy, hy', hyy, hroot, hq⟩ := GlobalTheory.OddRoot.exists_root_odd D p (hp.odd_of_ne_two h2) (x : AfE D)
      (k • w) (nsmul_mem hw k) (by rw [hwe, mul_smul]) hx
    refine ⟨Units.mkOfMulEqOne y y' hyy, ⟨hy, hy'⟩, hq, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hroot.symm)

end GlobalTheory.IdeleNinety
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundChosenFamilyOfIntrinsicHypothesesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexBoundChosenFamily_of_intrinsicHypotheses : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputs4_of_inputsR | exact GlobalTheory.FinalJoin.inputs4_of_inputsR | (intros; apply GlobalTheory.FinalJoin.inputs4_of_inputsR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundIntrinsicHypothesesNetBoundDegreeTwoStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_deg_two | exact GlobalTheory.FinalJoin.inputsR_deg_two | (intros; apply GlobalTheory.FinalJoin.inputsR_deg_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ → (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  first | exact @GlobalTheory.RealAverage.isAutFunSm_average | exact GlobalTheory.RealAverage.isAutFunSm_average | (intros; apply GlobalTheory.RealAverage.isAutFunSm_average <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PowMemRatOneSupCongOne
section
noncomputable section

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.CharFin
open scoped TensorProduct nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem unit_pow_card_cong (N : ℕ) (hN : 0 < N) (v : (hatRing F E)ˣ) :
    ∃ w : hatRing F E, (v : hatRing F E) ^ Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ - 1 = N * w := by
  have dec : ∀ x : hatRing F E, ∃ a : 𝓞 E, ∃ w : hatRing F E, x = diagInt F E a + (N : hatRing F E) * w := by
    intro x
    obtain ⟨a, w, hw, e⟩ := exists_int_add_nsmul F E N hN x x.2
    refine ⟨a, ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [e, nsmul_eq_mul]; simp; rfl
  obtain ⟨a, w, ea⟩ := dec v
  obtain ⟨b, w', eb⟩ := dec (v⁻¹ : (hatRing F E)ˣ)
  have hv : (v : hatRing F E) * (v⁻¹ : (hatRing F E)ˣ) = 1 := Units.mul_inv v
  let z : hatRing F E := -(diagInt F E a * w' + w * diagInt F E b + N * w * w')
  have h1 : diagInt F E (a * b - 1) = N * z := by
    rw [ea, eb] at hv
    rw [map_sub, map_mul, map_one]
    simp only [z]
    linear_combination hv
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : diag F E (((a * b - 1 : 𝓞 E) : E) / N) = z := by
    apply (isUnit_nat F E hN).mul_left_cancel
    rw [← map_natCast (diag F E), ← map_mul, mul_div_cancel₀ _ hN', map_natCast]
    have := congrArg (hatRing F E).subtype h1
    rw [map_mul, map_natCast] at this
    exact this
  obtain ⟨r, hr⟩ := GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E (x := ((a * b - 1 : 𝓞 E) : E) / N)
    (by rw [← diag_apply, h2]; exact z.2)
  have h3 : a * b - 1 = N * r := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_natCast, hr, mul_div_cancel₀ _ hN']
  let q := Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})
  have h4 : q a * q b = 1 := by
    rw [← map_mul, ← map_one q, Ideal.Quotient.eq, h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ with hk
  have h5 : (Units.mkOfMulEqOne _ _ h4) ^ k = 1 := pow_card_eq_one'
  have h6 : q (a ^ k) = q 1 := by
    rw [map_pow, map_one]
    exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h5)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h6)
  have h7 := congrArg (diagInt F E) hc
  rw [map_sub, map_pow, map_one, map_mul, map_natCast] at h7
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (v : hatRing F E) (diagInt F E a) k
  refine ⟨w * d + diagInt F E c, ?_⟩
  linear_combination hd + h7 + d * ea

variable (c : E ≃ₐ[F] E)

theorem pow_mem_ratOne_sup_congOne (hc : ∀ y, c (c y) = y) (N : ℕ) (hN : 0 < N) (x : (RA F E)ˣ)
    (hx : (x : RA F E) * bar c x = 1) :
    x ^ (2 * classNumber E * Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ) ∈ ratOne c ⊔ congOne c N := by
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ with hk
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber F E x
  have hst' : (s : RA F E) * t = 1 := congrArg Subtype.val hst
  have hbst : bar c s * bar c t = 1 := by rw [← map_mul, hst', map_one]
  have hcb : c b ≠ 0 := by simpa using hb
  have hq : b / c b ≠ 0 := div_ne_zero hb hcb
  let r : (RA F E)ˣ := (isUnit_diag F E hq).unit
  have hr : r ∈ ratOne c := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    change diag F E (b / c b) * diag F E (c (b / c b)) = 1
    rw [← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]
  let v : (hatRing F E)ˣ := Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩)
    (Subtype.ext (by
      change (s : RA F E) * bar c t * (t * bar c s) = 1
      linear_combination (bar c s * bar c t) * hst' + hbst))
  let u : (RA F E)ˣ := Units.map (hatRing F E).subtype.toMonoidHom v
  have hu : (u : RA F E) = s * bar c t := rfl
  have hun : (u : RA F E) * bar c u = 1 := by
    rw [hu, map_mul, bar_bar c hc]
    linear_combination (bar c s * bar c t) * hst' + hbst
  have hx2 : x ^ (classNumber E * 2) = r * u := by
    apply Units.ext
    have h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1 := by
      rw [map_pow, ← mul_pow, hx, one_pow]
    have h2 : diag F E (b / c b) * diag F E (c b) = diag F E b := by
      rw [← map_mul, div_mul_cancel₀ _ hcb]
    have h3 : bar c (diag F E b) = diag F E (c b) := rfl
    rw [e, map_mul, h3] at h1
    rw [Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]
    change _ = diag F E (b / c b) * _
    linear_combination (diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2
      - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst
  have huk : u ^ k ∈ congOne c N := by
    refine ⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩
    obtain ⟨w, hw⟩ := unit_pow_card_cong N hN v
    refine ⟨w, w.2, ?_⟩
    have := congrArg (hatRing F E).subtype hw
    rwa [map_sub, map_one, map_mul, map_natCast, map_pow] at this
  rw [mul_comm 2, pow_mul, hx2, mul_pow]
  exact Subgroup.mul_mem_sup (pow_mem hr k) huk

end GlobalTheory.NormOneChar

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open scoped TensorProduct

theorem tame_pow_eq_one : ∀ (D : D7) (N : ℕ) (xi : (AfE D)ˣ →* ℂˣ), 0 < N → (∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1) → (∀ x, NormOne x → CongOne N x → xi x = 1) → ∀ x, NormOne x → xi x ^ (2 * classNumber D.host.E * Nat.card (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)})ˣ) = 1 := by
  intro D N xi hN h1 h2 x hx
  have hc : ∀ (φ : D.host.E →+* ℂ) (y : D.host.E), φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y) :=
    fun φ y => @IsCMField.complexEmbedding_complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ φ y
  have hcc : ∀ y, GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y := fun y =>
    D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])
  have hcong : ∀ (x : (AfE D)ˣ), x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x := by
    intro x
    unfold CongOne
    simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
    exact Iff.rfl
  obtain ⟨r, ⟨⟨a, ha⟩, hr⟩, k, hk, e⟩ :=
    Subgroup.mem_sup.1 (pow_mem_ratOne_sup_congOne (GlobalTheory.Member.cF D) hcc N hN x hx)
  rw [← map_pow]
  have e' : xi (r * k) = 1 := by
    rw [map_mul, h1 r a ha hr, h2 k ((hcong k).1 hk).2 ((hcong k).1 hk).1, mul_one]
  rw [← e']
  exact congrArg xi e.symm

end GlobalTheory.NormOneChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RankOneOperatorMemOfTranslationAverageClosedStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  first | exact @GlobalTheory.TypeSum.rank_one_mem_of_closed | exact GlobalTheory.TypeSum.rank_one_mem_of_closed | (intros; apply GlobalTheory.TypeSum.rank_one_mem_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThreshol
section
set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem pageOK_of_pageRun_beyond : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  intro Z₀
  refine ⟨fun a b => max (Z₀ a b) (4 * b), ?_⟩
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP hx
  have hx1 : Z₀ H.CA H.CK ≤ large₂.sc.x := (le_max_left _ _).trans hx
  have hx2 : 4 * H.CK ≤ large₂.sc.x := (le_max_right _ _).trans hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  have hC : 1000 ≤ C2 := hd.1
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hxZ : large₂.sc.x ≤ zBase large₂ := hP.hyp.1.1.trans hfr
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have hZP : zBase large₂ ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have h1 : zBase large₂ ≤ zBase large₂ ^ A2 := by
      calc zBase large₂ = zBase large₂ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    exact h1.trans (le_mul_of_one_le_left (by linarith) (by linarith))
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := hZ1.trans hZP
  have hPP : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f := by
    have h1 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := by nlinarith
    exact h1.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hfrd := pageRun_sq_le_rd_and_eight_le_rank D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP
  exact ⟨⟨hP.hyp, hP.page, hP.tie, indexBoundConstant_le_pagePolynomial_of_runConditions D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hfrd.1, hfrd.2, three_le_DF_of_pageRun D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP,
    hx2.trans (hxZ.trans (hZP.trans hPP))⟩, hx1.trans hxZ⟩

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem volPairEx_and_finVol : ∀ (D : D7) (V : HSp D), V.SigOK → VolPairEx V ∧ Formalism.L2.Pj.FinVol V := by
  intro D V hs
  have h := GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ (tauE D) D.cd V
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hs
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h
  have hex : VolPairEx V := by
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hall μ hμ
    exact ⟨(μ, 𝓕), hμ, h𝓕⟩
  refine ⟨hex, ?_⟩
  have hp := volPair_isVolPair V hex
  have hm : (volPair V).1 (volPair V).2 =
      ENNReal.ofReal (GlobalTheory.Mem.Vol.trueVol D.sp.cm (tauE D) D.cd V) :=
    (hall _ hp.1).2 _ hp.2
  unfold Formalism.L2.Pj.FinVol
  rw [muQ_univ, hm]
  exact ⟨(ENNReal.ofReal_pos.2 (GlobalTheory.Mem.Vol.trueVol_pos _ _ _ _)).ne', ENNReal.ofReal_ne_top⟩

end GlobalTheory.FinalJoin2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open GlobalTheory.EX

theorem x_le_zBase_of_pow_le_n {D : D7} (L : SizeData₂ D) (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ)) :
    L.sc.x ≤ zBase L := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hL : 1 ≤ L.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow hx.le he.le
  have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hf : (D.R.n : ℝ) ≤ D.R.f := by
    unfold Ranks.f; exact_mod_cast (by omega : D.R.n ≤ 2 * D.R.n)
  have hr : (1 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hxf : L.sc.x ≤ (D.R.f : ℝ) := h1.trans (hn.trans hf)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  unfold zBase
  calc L.sc.x ≤ (D.R.f : ℝ) * 1 * 1 := by linarith
    _ ≤ _ := by gcongr

end GlobalTheory.FinalJoin2

end
end

