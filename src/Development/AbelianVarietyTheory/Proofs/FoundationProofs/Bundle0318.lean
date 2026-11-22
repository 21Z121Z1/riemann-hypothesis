import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0011
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.NormLeOneOfIntegralInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEqStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ → U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  first | exact @GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | exact GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | (intros; apply GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    ∃ x : E, y - (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    rw [TensorProduct.tmul_add, add_sub_add_comm]
    exact add_mem hx hx'
  | tmul a e =>
    obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he' : IsIntegral ℤ (m • e) := he e (Finset.mem_singleton_self e)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have hcont : Continuous fun z : Fv F v => (m : F)⁻¹ • a - z := continuous_sub_left _
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v).exists_mem_open
      (hO.preimage hcont) ⟨(m : F)⁻¹ • a, by simp⟩
    refine ⟨k • (m • e), ?_⟩
    have hk' : (m : F)⁻¹ • a - algebraMap F (Fv F v) k ∈ v.adicCompletionIntegers F := hk
    have h := tmul_mem_intLoc (E := E) hk' ⟨m • e, he'⟩
    convert h using 1
    change _ = ((m : F)⁻¹ • a - algebraMap F (Fv F v) k) ⊗ₜ[F] (m • e)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul F m e, inv_smul_smul₀ hmF]

theorem isIntegral_of_absBar_le_one (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1) :
    ∃ p : Polynomial (v.valuationSubringAtPrime F), p.Monic ∧
      p.eval₂ ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype) x = 0 := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have h1 : (minpoly F x).map (algebraMap F (FvBar F v)) ∈ Polynomial.lifts (valBar F v).integer.subtype := by
    refine Polynomial.Splits.mem_lift_of_roots_mem_range (IsAlgClosed.splits _) (hmon.map _) _ fun a ha => ?_
    have ha' : a ∈ (minpoly F x).rootSet (FvBar F v) := by
      rw [Polynomial.rootSet_def]; simpa [Polynomial.aroots_def] using ha
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at ha'
    obtain ⟨τ, rfl⟩ := ha'
    exact ⟨⟨τ x, hx τ⟩, rfl⟩
  have h2 : minpoly F x ∈ Polynomial.lifts (v.valuationSubringAtPrime F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have h3 : absBar F v (algebraMap F (FvBar F v) ((minpoly F x).coeff n)) ≤ 1 := by
      rw [← Polynomial.coeff_map, ← hc]; exact c.2
    rw [IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), absBar_algebraMap] at h3
    have h4 : Valued.v (algebraMap F (Fv F v) ((minpoly F x).coeff n)) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h3)
    refine ⟨⟨(minpoly F x).coeff n, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le h4
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic h2 hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq]
  exact minpoly.aeval F x

theorem one_tmul_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1) : (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  let : Algebra (v.valuationSubringAtPrime F) E :=
    ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype).toAlgebra
  have : IsScalarTower (𝓞 F) (v.valuationSubringAtPrime F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (v.valuationSubringAtPrime F) x :=
    isIntegral_of_absBar_le_one v x fun τ => by simpa using (absFin_le_iff F v).1 hx τ
  obtain ⟨⟨s, hs⟩, h2⟩ := IsIntegral.exists_multiple_integral_of_isLocalization v.asIdeal.primeCompl x h1
  have h3 : IsIntegral ℤ ((s : F) • x) := isIntegral_trans _ h2
  have hv : v.valuation F (s : F) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hs0 : (s : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have h := tmul_mem_intLoc (E := E) h4 ⟨_, h3⟩
  convert h using 1
  change _ = (algebraMap F (Fv F v) (s : F)⁻¹) ⊗ₜ[F] ((s : F) • x)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hs0]

theorem mem_intLoc_iff_absFin_le_one {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ absFin F v y ≤ 1 := by
  refine ⟨absFin_le_one_of_mem_intLoc, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v y
  have h1 : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1 := by
    have := absFin_add_le F v y (-(y - (1 : Fv F v) ⊗ₜ[F] x))
    rw [absFin_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    exact this.trans (max_le hy (absFin_le_one_of_mem_intLoc hx))
  simpa using add_mem hx (one_tmul_mem_intLoc v x h1)

theorem algebraMap_basis_repr {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ y * τ (b i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
  | tmul a e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      trace_eq_sum_embeddings, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finEmb_tmul, map_mul]; ring

theorem absFin_eq_zero_iff {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} : absFin F v y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun h => by rw [h, absFin_zero]⟩
  have h0 : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ y = 0 := fun τ =>
    (absBar_eq_zero F v).1 (le_antisymm ((absFin_le_iff F v).1 hy.le τ) zero_le)
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (Fv F v) b.traceDual).ext_elem fun i => ?_
  refine (algebraMap (Fv F v) (FvBar F v)).injective ?_
  rw [algebraMap_basis_repr]
  simp [h0]

theorem normFin_le_one_iff {v : HeightOneSpectrum (𝓞 F)} {m n : Type} [Fintype m] [Fintype n]
    {y : Matrix m n (Fv F v ⊗[F] E)} : normFin F v y ≤ 1 ↔ ∀ i j, y i j ∈ intLoc F E v := by
  simp only [normFin_le_iff, mem_intLoc_iff_absFin_le_one]

theorem mem_stabLoc_stdLattice_iff_htFin_eq_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E n) v ↔ htFin F v (matHom _ σ J g) = 1 := by
  rw [htFin, htOf_eq_one]
  constructor
  · intro hg
    have h1 := normFin_conj_le_one isLatticeFrame_one hg
    have h2 := normFin_conj_le_one isLatticeFrame_one (inv_mem hg)
    rw [map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [map_inv] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), normFin F v M ≤ 1 → ∀ y,
        y ∈ latLoc F (stdLattice E n) v → M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
      mem_latLoc_stdLattice.2 fun i => by
        change ∑ j, M i j * y j ∈ _
        exact sum_mem fun j _ => mul_mem (normFin_le_one_iff.1 hM i j) (mem_latLoc_stdLattice.1 hy j)
    refine mem_stabLoc.2 fun y => ⟨key _ h1 y, fun hy => ?_⟩
    have := key _ h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem intLoc_absFin_htFin (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) :
    (∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔ absFin F v y ≤ 1) ∧
    (∀ y : Fv F v ⊗[F] E, absFin F v y = 0 ↔ y = 0) ∧
    ∀ g : GLoc σ J v, g ∈ stabLoc σ J (stdLattice E n) v ↔ htFin F v (matHom _ σ J g) = 1 :=
  ⟨fun _ => mem_intLoc_iff_absFin_le_one, fun _ => absFin_eq_zero_iff,
    fun _ => mem_stabLoc_stdLattice_iff_htFin_eq_one⟩

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransportStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_parameter_series_deriv_transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative ℂ_[p] (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  first | exact @GlobalTheory.DerivTransport.atU_deriv | exact GlobalTheory.DerivTransport.atU_deriv | (intros; apply GlobalTheory.DerivTransport.atU_deriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMNormPhi

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem intSer_iff' {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem intSer_sq_of_eq (h F f L : PowerSeries ℂ_[p]) (τ : ℂ_[p]) (n : ℕ) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : coeff 1 h = τ) (hτ : ‖τ‖ = 1) (hF : constantCoeff F = 1)
    (hL : IntSer L) (hL0 : constantCoeff L = 1)
    (e : h ^ 2 * F ^ 2 = C (τ ^ 2) * X ^ 2 * (f ^ n) ^ 2 * L) : IntSer ((F⁻¹ * f ^ n) ^ 2) := by
  obtain ⟨v, rfl⟩ := (PowerSeries.X_dvd_iff).2 hh0
  have hv : IntSer v := fun m => by simpa [PowerSeries.coeff_succ_X_mul] using hh (m + 1)
  have e' : v ^ 2 * F ^ 2 = C (τ ^ 2) * (f ^ n) ^ 2 * L := by
    have hX : (X : PowerSeries ℂ_[p]) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    linear_combination e
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hFi : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel _ (by rw [hF]; exact one_ne_zero)
  have hLi : L * L⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hL0]; exact one_ne_zero)
  have hc : C (τ⁻¹ ^ 2) * C (τ ^ 2) = (1 : PowerSeries ℂ_[p]) := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, map_one]
  have key : (F⁻¹ * f ^ n) ^ 2 = C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ := by
    linear_combination (-(C (τ⁻¹ ^ 2)) * F⁻¹ ^ 2 * L⁻¹) * e' +
      (C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ * (F⁻¹ * F + 1)) * hFi -
      (F⁻¹ ^ 2 * (f ^ n) ^ 2 * L * L⁻¹) * hc - (F⁻¹ ^ 2 * (f ^ n) ^ 2) * hLi
  obtain ⟨hr, -, hC, -, hinv, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  rw [key]
  refine (hr _ _ (hr _ _ ((hC _).2 ?_) (by rw [sq]; exact (hr _ _ hv hv).2.2)).2.2
    (hinv L hL (by rw [hL0, norm_one]))).2.2
  rw [norm_pow, norm_inv, hτ]; simp

theorem atU_prod' (g : GL3Theta.G1 p) {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    refine ⟨h1, ?_⟩
    rw [h2, lamC, dif_pos (one_mem _)]
    exact congrArg C (map_one g.lam)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact ((GlobalTheory.SerTransport.transport p g).1 _ _ (hF a) ih.1).1

theorem phAt_mulBy_norm : ∀ (D : D7), GL3Theta.endInt D → GL3Theta.addInt D → ∀ (p : ℕ) [Fact p.Prime]
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → p ≠ 2 →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    GL3Theta.Simeq (g.phAt (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (GL3Theta.tauK D g.lam (a : D.host.K) * GL3Theta.tauKc D g.lam (a : D.host.K)) *
        g.phAt (GL3Theta.Xv ())) := by
  intro D hend _ p _ cc δ g hg hp a hcop
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halgσ : AlgEnt (sgStar g.abelian₂) := by
    have e : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by funext z; simp [U1]
    have := huse 0 ⟨1, one_pos, by simp⟩
    rw [e] at this
    exact ⟨hlat'.differentiable, this⟩

  set β : ℂ := D.host.φ₀ ((a : D.host.K) : D.host.E) with hβdef
  have hβQ : β ∈ Qbar := Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _
  have hβst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := hst a
  let a' : 𝓞 D.host.K := ⟨Formalism.MainNotions.Ext.conjK D (a : D.host.K),
    (RingOfIntegers.isIntegral_coe a).map (Formalism.MainNotions.Ext.conjK D).toIntAlgHom⟩
  have hconj : D.host.φ₀ ((a' : D.host.K) : D.host.E) = starRingEnd ℂ β := by
    show D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E) = _
    rw [Formalism.MainNotions.Ext.conjK_coe]
    exact D.host.conjE_apply D.host.φ₀ _
  have hN : β * starRingEnd ℂ β = ((Algebra.norm ℤ a : ℤ) : ℂ) := by
    have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a
    rw [Algebra.intNorm_eq_norm] at h
    have h' := congrArg D.host.φ₀ h
    have hc : D.host.φ₀ (D.host.conj ((a : D.host.K) : D.host.E)) = starRingEnd ℂ β :=
      D.host.conjE_apply D.host.φ₀ _
    rw [map_intCast, map_mul, hc] at h'
    exact h'.symm
  have hnn : 0 ≤ (Algebra.norm ℤ a : ℤ) := by
    have e1 : ((Algebra.norm ℤ a : ℤ) : ℂ) = ((Complex.normSq β : ℝ) : ℂ) := by
      rw [← hN, Complex.mul_conj]
    have e2 : ((Algebra.norm ℤ a : ℤ) : ℝ) = Complex.normSq β := by exact_mod_cast e1
    have := Complex.normSq_nonneg β
    rw [← e2] at this
    exact_mod_cast this
  have hn0 : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).one_lt.ne' hcop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hnk : (Algebra.norm ℤ a : ℤ) = ((k + 1 : ℕ) : ℤ) := by
    have := Int.natAbs_of_nonneg hnn
    rw [hk] at this
    exact this.symm
  have hβN : β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) := by rw [hN, hnk]; push_cast; ring
  have hcop' : Nat.Coprime (k + 1) p := by
    have := hcop
    rwa [hk] at this

  set τ := GL3Theta.tauK D g.lam (a : D.host.K) with hτdef
  have hτβ : τ = lamC g.lam β := rfl
  have htn : τ * GL3Theta.tauKc D g.lam (a : D.host.K) = ((k + 1 : ℕ) : ℂ_[p]) := by
    rw [hτdef, Formalism.MainNotions.Ext.CutA.tau_norm, hnk]; push_cast; ring
  have hτ1 : ‖τ‖ ≤ 1 := by
    rw [hτβ, hβdef, ← Formalism.MainNotions.Ext.tauKp_apply]; exact PI.OkpW.norm_tau_le _ a
  have hτc1 : ‖GL3Theta.tauKc D g.lam (a : D.host.K)‖ ≤ 1 := by
    have e : GL3Theta.tauKc D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a' : D.host.K) := by
      rw [Formalism.MainNotions.Ext.tauKp_apply]
      show _ = lamC g.lam (D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E))
      rw [Formalism.MainNotions.Ext.conjK_coe]; rfl
    rw [e]; exact PI.OkpW.norm_tau_le _ a'
  have hn1 : ‖((k + 1 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hcop'.symm
  have hτu : ‖τ‖ = 1 := by
    have := congrArg norm htn
    rw [norm_mul, hn1] at this
    nlinarith [norm_nonneg τ, norm_nonneg (GL3Theta.tauKc D g.lam (a : D.host.K))]

  obtain ⟨hmul, hconst, -, hscale⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := hscale hok β hβQ
  obtain ⟨hu, hw, hw0, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hhI : IntSer h := by
    have := hend p cc δ g hg' (τ, GL3Theta.tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)
    have h' : IntegralMv (h : MvPowerSeries Unit ℂ_[p]) := by rw [hh]; exact this
    exact intSer_iff'.1 h'

  set f := ePhi1 g.lam g.abelian₂ g.C g.wq with hfdef
  have hε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  obtain ⟨Q, hQ, hfac⟩ := GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients g.abelian₂ hlat' β k hβst hβN
  have hLaQ : ∀ i, ((k + 1 : ℕ) : ℂ) * Q i ∈ g.abelian₂ := fun i => by
    have e : ((k + 1 : ℕ) : ℂ) * Q i = D.host.φ₀ ((a' : D.host.K) : D.host.E) * (β * Q i) := by
      rw [hconj, ← hβN]; ring
    rw [e]; exact hst a' _ (hQ i).2
  have hsq : ∀ i, AlgEnt (sqTh g.abelian₂ (Q i)) ∧
      g.atU (sqTh g.abelian₂ (Q i)) = f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)) :=
    fun i => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 halgσ (Q i) (hQ i).1
      (hwp _ ⟨k + 1, Nat.succ_pos k, hLaQ i⟩ (hQ i).1).1
  have hx : ∀ i, ‖xAt g (Q i)‖ ≤ 1 := fun i =>
    GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime D p cc δ g hg' (k + 1) (Q i) (Nat.succ_pos k) hcop' (hLaQ i) (hQ i).1
  obtain ⟨hr, -, hC, hXI, -, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hlineI : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → IntSer (lineSer g.wq⁻¹ x) := fun x hx =>
    (hr _ _ hw ((hr _ _ ((hC x).2 hx) (by rw [sq]; exact (hr _ _ hXI hXI).2.2)).2.2)).2.1
  have hLI : IntSer (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) :=
    Finset.prod_induction _ IntSer (fun _ _ h1 h2 => (hr _ _ h1 h2).2.2)
      (fun n => by rw [coeff_one]; split_ifs <;> simp) (fun i _ => hlineI _ (hx i))
  have hL0 : constantCoeff (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) = 1 := by
    rw [map_prod]; refine Finset.prod_eq_one fun i _ => ?_
    simp only [lineSer, map_sub, map_mul, map_pow, constantCoeff_X, hw0, constantCoeff_C]; simp

  have hA := hsub _ halgσ
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have lhs : g.atU (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
      (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * h * subst h f) ^ 2 := by
    have e := (hmul _ _ hA.1 hA.1).1.2
    have e2 : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => sgStar g.abelian₂ (β * z) * sgStar g.abelian₂ (β * z) := by
      funext z; ring
    rw [e2, e, hA.2, hσ, subst_mul hs, subst_mul hs, subst_C, subst_X hs, sq]
    rfl
  have hτ2 : lamC g.lam (β ^ 2) = τ ^ 2 := by
    have e : β ^ 2 = D.host.φ₀ (((a : D.host.K) * (a : D.host.K) : D.host.K) : D.host.E) := by
      rw [IntermediateField.coe_mul, map_mul, sq]
    rw [e, sq]
    exact Formalism.MainNotions.Ext.CutA.tauK_mul D g.lam _ _
  have hG2 : AlgEnt (fun z => sgStar g.abelian₂ z ^ 2) ∧
      g.atU (fun z => sgStar g.abelian₂ z ^ 2) = g.atU (sgStar g.abelian₂) ^ 2 := by
    have e2 : (fun z => sgStar g.abelian₂ z ^ 2) = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z := by funext z; ring
    rw [e2, sq]; exact (hmul _ _ halgσ halgσ).1
  have hP := atU_prod' g Finset.univ (fun i => (hsq i).1)
  have hGP := (hmul _ _ hG2.1 hP.1).1
  have hc := hconst (β ^ 2) (pow_mem hβQ 2)
  have hcGP := (hmul _ _ hc.1 hGP.1).1
  have rhs : g.atU (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
      C (τ ^ 2) * ((C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * f) ^ 2 *
        ∏ i, (f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)))) := by
    have e2 : (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
        fun z => β ^ 2 * (sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) := by funext z; ring
    rw [e2, hcGP.2, hc.2, hGP.2, hG2.2, hP.2, hσ, hτ2, Finset.prod_congr rfl fun i _ => (hsq i).2]
  have E1 := congrArg g.atU (funext hfac : (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
    fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)
  rw [lhs, rhs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at E1
  have e : h ^ 2 * (subst h f : PowerSeries ℂ_[p]) ^ 2 =
      C (τ ^ 2) * X ^ 2 * (f ^ (k + 1)) ^ 2 * ∏ i, lineSer g.wq⁻¹ (xAt g (Q i)) := by
    have hε2 : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ^ 2 ≠ 0 :=
      pow_ne_zero _ fun h0 => hε0 (by simpa using congrArg constantCoeff h0)
    apply mul_left_cancel₀ hε2
    linear_combination E1
  have hF0 : constantCoeff (subst h f : PowerSeries ℂ_[p]) = 1 := by
    rw [GlobalTheory.SerTransport.const_subst hh0, hE]
  have hI2 := intSer_sq_of_eq h (subst h f) f _ τ (k + 1) hhI hh0 hh1 hτu hF0 hLI hL0 e
  have hH0 : constantCoeff ((subst h f : PowerSeries ℂ_[p])⁻¹ * f ^ (k + 1)) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_inv, hF0, map_pow, hE]; simp
  have hI := GlobalTheory.T.padicComplex_integral_of_sq_integral_odd p hp _ hH0 hI2
  obtain ⟨c0, ex⟩ := GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div p g h (k + 1) hE hh0
  have hmb : (g.mulBy τ (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = h := hh.symm
  rw [hmb, htn]
  refine ⟨c0, ?_⟩
  rw [ex]
  exact intSer_iff'.2 hI
end GlobalTheory.CMNormPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruenceStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  first | exact @GlobalTheory.pair_edge_dlog | exact GlobalTheory.pair_edge_dlog | (intros; apply GlobalTheory.pair_edge_dlog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  first | exact @GlobalTheory.FrobStick.colAB_atU | exact GlobalTheory.FrobStick.colAB_atU | (intros; apply GlobalTheory.FrobStick.colAB_atU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative ℂ_[p] (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  first | exact @GlobalTheory.FrobStick.colC_atU | exact GlobalTheory.FrobStick.colC_atU | (intros; apply GlobalTheory.FrobStick.colC_atU <;> assumption)
end

