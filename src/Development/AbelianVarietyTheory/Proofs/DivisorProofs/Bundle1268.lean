import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TensFockInfPhysSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.GramTwistNorm

open GlobalTheory.UnitLemma

theorem phi_map (a : ℕ) {R : Type} [CommRing R] (c : R →+* R) :
    (GlobalTheory.Tw.Phi a R).map c = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) :=
  _root_.UpperTheory.Reformulated.B.Yzd3.phi_mul_self a

theorem phi_mul_transpose (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 :=
  _root_.UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose a

theorem herm_sum_left {K : UQ} (B : InvAlg K) (β : B.A) {ι : Type} (s : Finset ι) (v : ι → K.E)
    (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_sum_right {K : UQ} (B : InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι) (r : ι → K.E)
    (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  simp only [InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_det_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (β : B.Aˣ) {a : ℕ}
    (b : Module.Basis (Fin a) K.E B.A) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set y := ∑ i, v i • b i with hy
  have hy0 : y ≠ 0 := by
    intro hy'
    apply hv0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hy' i
  have hyb : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, herm_sum_left]
    exact this
  have hyz : ∀ z, B.herm β y z = 0 := by
    intro z
    rw [← b.sum_repr z, herm_sum_right]
    simp [hyb]
  have hβy : (β : B.A) * y = 0 := by
    apply GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hsep
    intro w
    have := hyz (B.σ w)
    simp only [InvAlg.herm, B.σ_σ] at this
    exact this
  exact hy0 ((Units.mul_right_eq_zero β).1 hβy)

theorem gram_map_conj {K : UQ} (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (hec : ∀ x, e (K.c x) = c (e x)) (a : ℕ) (β : B.A)
    (hβ : B.σ β = β * ((-1) ^ (a - 1) * B.g)) (b : Module.Basis (Fin a) K.E B.A) :
    ((Matrix.of fun i j => B.herm β (b i) (b j)).map e).map c =
      ((-1 : L) ^ (a - 1)) • (((Matrix.of fun i j => B.herm β (b i) (b j)).map e)ᵀ *
        (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e) :=
  _root_.GlobalTheory.ScalarSigmaBasis.main B L e c hec a β hβ b

theorem gram_twisted_norm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  intro K B L _ e c hec hcc a Q hPQ hQs hQd β hβ b
  set S : Matrix (Fin a) (Fin a) K.E := Matrix.of fun i j => B.herm β (b i) (b j) with hS
  have hG : (Matrix.of fun i j => e (B.herm β (b i) (b j))) = S.map e := rfl
  have hsep : B.P.Separable := by rw [hPQ]; exact hQs.map
  rw [hG]
  refine ⟨?_, ?_⟩
  · have hdet : (S.map e).det = e S.det := by
      rw [show S.map e = (e : K.E →+* L).mapMatrix S from rfl, ← RingHom.map_det]
      rfl
    rw [hdet, isUnit_iff_ne_zero]
    exact (map_ne_zero e).2 (gram_det_ne_zero B hsep β b)
  · intro δ hδ
    set G := S.map e with hGdef
    set P := (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e with hP
    set Φ := GlobalTheory.Tw.Phi a L with hΦ
    have hGc : G.map c = ((-1 : L) ^ (a - 1)) • (Gᵀ * P) := gram_map_conj B L e c hec a β hβ b
    have hinv : (δ⁻¹).val = Φ * Gᵀ := by
      have h1 : (δ.val * Φ)⁻¹ = Gᵀ := by rw [← hδ, Matrix.transpose_transpose]
      have hΦinv : Φ⁻¹ = Φᵀ := Matrix.inv_eq_right_inv (phi_mul_transpose a)
      rw [Matrix.mul_inv_rev, hΦinv, ← Matrix.coe_units_inv] at h1
      calc (δ⁻¹).val = Φ * Φᵀ * (δ⁻¹).val := by rw [hΦ, phi_mul_transpose, Matrix.one_mul]
        _ = Φ * Gᵀ := by rw [Matrix.mul_assoc, h1]
    have hθ : (thetaGL a c δ).val = Φ * ((δ⁻¹).val.map c)ᵀ * Φᵀ := rfl
    have hΦΦ : Φᵀ * Φᵀ = ((-1 : L) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) L) := by
      rw [← Matrix.transpose_mul, hΦ, phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
    have hδΦ : δ.val * Φ * Gᵀ = 1 := by rw [Matrix.mul_assoc, ← hinv, Units.mul_inv]
    have key : (δ * thetaGL a c δ).val = P := by
      rw [Units.val_mul, hθ, hinv, Matrix.map_mul, hΦ, phi_map, ← hΦ, Matrix.transpose_mul,
        Matrix.transpose_map, Matrix.transpose_transpose, hGc]
      calc δ.val * (Φ * ((-1 : L) ^ (a - 1) • (Gᵀ * P) * Φᵀ) * Φᵀ)
          = ((-1 : L) ^ (a - 1)) • ((δ.val * Φ * Gᵀ) * P * (Φᵀ * Φᵀ)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = P := by
            rw [hδΦ, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
              neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, hP, show (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e =
      (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map (e : K.E →+* L) from rfl,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    change B.P.map (e : K.E →+* L) = Q
    rw [hPQ, Polynomial.map_map]
    have : (e : K.E →+* L).comp e.symm.toRingHom = RingHom.id L := by
      ext x; simp
    rw [this, Polynomial.map_id]

end GlobalTheory.GramTwistNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightKernelLowestType
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem highestWeightKernel_lowestType : AlgDatum := by
  intro n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS

  have hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z := by
    have e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) =
        fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
      funext a b
      simp only [diagE, eT, sgE_cpT]
    rw [← e]; exact hz
  obtain ⟨s, hy0, hy⟩ := khw_extract ε hg.1 hz' hz0
  set y := tcoef ((fockBasis n).coord s) z with hydef

  have hs : s ⊆ lfPhysModes ε := by
    intro m hm
    by_contra hnm
    apply hy0
    refine tco_physSub_zero hzp hm fun hp => hnm ?_
    obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
    rw [Equiv.symm_apply_apply] at hp
    exact (lf_mem_phys ε x.1 x.2).2 hp
  set Ph := gcPh ε s with hPh
  have hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph := by
    rw [gc_wt_eq ε hs]
    funext a
    simp only [gaW, lowK, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hwt] at hy
  have hyS : y ∈ S := hzS s
  set V := kLowSpan ε E y with hV
  have hVS : V ≤ S := kLowSpan_le hSk hyS
  haveI : FiniteDimensional ℂ S := hSfd
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V := kLowSpan_kIrrHW hE hU hy hy0 hVfd

  set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT
  have hTk : IsKStableSub ε E T := by
    intro a b _ v hv
    rw [hT, LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at hc
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [hc, sub_eq_zero.1 hv, map_smul, sub_self]
  have hyT : y ∈ T := by
    rw [hT, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hcas s, sub_self]
  have hVT : V ≤ T := kLowSpan_le hTk hyT
  have hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    have := hVT hv
    rw [hT, LinearMap.mem_ker] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this

  have hPh0 : Ph = ∅ := by
    by_contra hne
    exact dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc
  rw [hPh0] at hVirr
  simp only [phSum, Finset.sum_empty, sub_zero] at hVirr
  refine ⟨V, hVirr, ?_, hVc⟩
  intro h0
  apply hy0
  have : y ∈ V := self_mem_kLowSpan y
  rw [h0] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem homFixRep_glue_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB J U hU hloc
  refine GlobalTheory.T.homFixedPullback_representable_glue (fun H A B _ _ _ _ L M Φ hΦ hA hB hL hM rA rB h => GlobalTheory.HomFixLocal.lbIso_pull_of_local H A B L M Φ hΦ hA hB hL hM rA rB h) S A B L M hA hB hL hM rA rB J (fun i => (U i).toScheme) (fun i => (U i).ι) (fun i => inferInstance) (fun s => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hU s; exact ⟨i, by simpa [Scheme.Opens.range_ι] using hi⟩
  · obtain ⟨AU, gA, BU, gB, φA, φB, pA, pB, R, h1, h2, h3⟩ := hloc i; exact ⟨AU, BU, gA, gB, φA, φB, R, pA, pB, h1, h2, h3⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealCountUnderExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem ideal_le_prime_pow_iff_le_count {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) (n : ℕ) :
    J ≤ v.asIdeal ^ n ↔ n ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  classical
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

theorem count_map_ideal_eq_mul_of_valuation_pow (k k' : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] (i : k →+* k') (J : Ideal (𝓞 k)) (𝔭 : HeightOneSpectrum (𝓞 k))
    (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ)
    (h : ∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) :
    FractionalIdeal.count k' 𝔓 ((J.map (RingOfIntegers.mapRingHom i) : Ideal (𝓞 k')) :
      FractionalIdeal (nonZeroDivisors (𝓞 k')) k') =
    ε * FractionalIdeal.count k 𝔭 (J : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  classical
  by_cases hJ : J = 0
  · subst hJ
    simp [FractionalIdeal.count_zero]
  have hv : ∀ x : 𝓞 k, 𝔓.intValuation (RingOfIntegers.mapRingHom i x) = 𝔭.intValuation x ^ ε := by
    intro x
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := k'),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := k), ← h]
    rfl
  have hinj : Function.Injective (RingOfIntegers.mapRingHom i) := by
    intro x y hxy
    apply RingOfIntegers.ext
    apply i.injective
    exact congrArg (fun t : 𝓞 k' => (t : k')) hxy
  have hJ' : J.map (RingOfIntegers.mapRingHom i) ≠ 0 := fun h0 =>
    hJ ((Ideal.map_eq_bot_iff_of_injective hinj).mp h0)
  rw [FractionalIdeal.count_coe k' 𝔓 hJ', FractionalIdeal.count_coe k 𝔭 hJ]
  set m := (Associates.mk 𝔭.asIdeal).count (Associates.mk J).factors with hm
  set m' := (Associates.mk 𝔓.asIdeal).count
    (Associates.mk (J.map (RingOfIntegers.mapRingHom i))).factors with hm'
  have hle : J ≤ 𝔭.asIdeal ^ m := (ideal_le_prime_pow_iff_le_count 𝔭 hJ m).mpr le_rfl
  have hle' : J.map (RingOfIntegers.mapRingHom i) ≤ 𝔓.asIdeal ^ m' :=
    (ideal_le_prime_pow_iff_le_count 𝔓 hJ' m').mpr le_rfl
  have hnle : ¬ J ≤ 𝔭.asIdeal ^ (m + 1) := fun h1 => by
    have := (ideal_le_prime_pow_iff_le_count 𝔭 hJ (m + 1)).mp h1
    omega
  have h1 : ε * m ≤ m' := by
    apply (ideal_le_prime_pow_iff_le_count 𝔓 hJ' _).mp
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← 𝔓.intValuation_le_pow_iff_mem, hv]
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    refine (pow_le_pow_left' hx' ε).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    push_cast
    simp
  have h2 : m' ≤ ε * m := by
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnle
    have hx0 : x ≠ 0 := fun h0 => hxn (h0 ▸ zero_mem _)
    rw [← 𝔭.intValuation_le_pow_iff_mem, not_le] at hxn
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    have h3 := (𝔓.intValuation_le_pow_iff_mem _ m').mpr (hle' (Ideal.mem_map_of_mem _ hx))
    rw [hv] at h3
    have hne : 𝔭.intValuation x ≠ 0 := 𝔭.intValuation_ne_zero x hx0
    rw [← WithZero.exp_log hne] at hxn hx' h3
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp] at h3
    rw [WithZero.exp_lt_exp] at hxn
    rw [WithZero.exp_le_exp] at hx'
    have h4 : WithZero.log (𝔭.intValuation x) = -(m : ℤ) := by
      push_cast at hxn
      omega
    rw [h4, nsmul_eq_mul] at h3
    have : (m' : ℤ) ≤ ε * m := by linarith
    exact_mod_cast this
  have : m' = ε * m := le_antisymm h2 h1
  rw [this]
  push_cast
  ring

theorem count_map_comp_ideal_eq_mul_of_valuation_pow : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  intro E _ _ k k' _ _ _ _ i τ 𝔞 𝔭 𝔓 ε h
  have hc : RingOfIntegers.mapRingHom (i.comp τ) =
      (RingOfIntegers.mapRingHom i).comp (RingOfIntegers.mapRingHom τ) := by
    ext x
    rfl
  rw [hc, ← Ideal.map_map]
  exact count_map_ideal_eq_mul_of_valuation_pow k k' i _ 𝔭 𝔓 ε h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

def HasDieu : Prop :=
  ∃ (D : C.Modules) (g : ℕ) (ρ : O →+* End D) (a : omega G ⟶ D) (b : D ⟶ Lie G)
    (u : frobTwist q k (Lie G) ⟶ D) (v : D ⟶ frobTwist q k (omega G)) (w₁ : a ≫ b = 0) (w₂ : u ≫ v = 0),
    IsVB (omega G) g ∧ IsVB D (2 * g) ∧ (ShortComplex.mk a b w₁).ShortExact ∧ (ShortComplex.mk u v w₂).ShortExact ∧
    IsEquivariant (omegaAct i) ρ a ∧ IsEquivariant ρ ((lieAct i).comp c) b ∧
    IsEquivariant (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k))) ρ u ∧
    IsEquivariant ρ (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) v

def HasSeq : Prop :=
  ∃ (H : (O →+* k) → C.Modules) (rL rH : (O →+* k) → ℕ) (D : C.Modules) (g : ℕ),
    (∀ σ, IsVB (lieSub i (scal C σ)) (rL σ)) ∧ (∀ σ, IsVB (H σ) (rH σ)) ∧
    (∀ σ, IsExtension (dual (lieSub i (scal C σ))) (H σ) (lieSub i (scal C (σ.comp c)))) ∧
    (∀ σ, IsExtension (frobTwist q k (lieSub i (scal C (σ.comp c)))) (H ((frobenius k q).comp σ))
      (frobTwist q k (dual (lieSub i (scal C σ))))) ∧
    IsVB (Lie G) g ∧ IsVB D (2 * g) ∧ IsExtension (dual (Lie G)) D (Lie G) ∧
    (∃ v : frobTwist q k (Lie G) ⟶ D, Mono v) ∧
    Nonempty (Lie G ≅ ∐ fun σ : O →+* k => lieSub i (scal C (σ.comp c)))

def DegRel [IsIntegral C] {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] {G' : Over C'} [GrpObj G']
    [QuasiSeparated G'.hom] (i' : OAct O G') (m : ℕ) : Prop :=
  (∀ σ : O →+* k, deg k (lieSub i' (scal C' σ)) = m * deg k (lieSub i (scal C σ))) ∧
    ∀ d ∈ subDegs k (Lie G), ∃ d' ∈ subDegs k (Lie G'), m * d ≤ d'

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

def intEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (Formalism.L2.Pj.embF c τ)

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

theorem DegRel.trans {k : Type} [Field k] {C C' C'' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)]
    [Algebra k Γ(C'', ⊤)] [IsIntegral C] [IsIntegral C'] [IsIntegral C''] {G : Over C} [GrpObj G] [QuasiSeparated G.hom]
    {G' : Over C'} [GrpObj G'] [QuasiSeparated G'.hom] {G'' : Over C''} [GrpObj G''] [QuasiSeparated G''.hom]
    {i : OAct O G} {i' : OAct O G'} {i'' : OAct O G''} {m n : ℕ} (h : DegRel k i i' m) (h' : DegRel k i' i'' n) :
    DegRel k i i'' (n * m) := by
  refine ⟨fun σ => by rw [h'.1, h.1]; push_cast; ring, fun d hd => ?_⟩
  obtain ⟨d', hd', e⟩ := h.2 d hd
  obtain ⟨d'', hd'', e'⟩ := h'.2 d' hd'
  refine ⟨d'', hd'', le_trans ?_ e'⟩
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left e (Nat.cast_nonneg _)

theorem DegRel.refl {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C] {G : Over C} [GrpObj G]
    [QuasiSeparated G.hom] (i : OAct O G) : DegRel k i i 1 :=
  ⟨fun _ => by simp, fun d hd => ⟨d, hd, by simp⟩⟩

example (k : Type) [Field k] : Splits ℤ k :=
  ⟨Unit, inferInstance, fun _ => Int.castRingHom k, isSplitBy_of_injective (fun _ _ _ => rfl) (by simp)⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDiscStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc : IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poincare_disc | exact GlobalTheory.GoodTop.integrableOn_poincare_disc | (intros; apply GlobalTheory.GoodTop.integrableOn_poincare_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w n → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  first | exact @GlobalTheory.SplitUniq.splitUniq | exact GlobalTheory.SplitUniq.splitUniq | (intros; apply GlobalTheory.SplitUniq.splitUniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  first | exact @GlobalTheory.BCT.OrbitT.orbit_main | exact GlobalTheory.BCT.OrbitT.orbit_main | (intros; apply GlobalTheory.BCT.OrbitT.orbit_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  first | exact @GlobalTheory.FlagPush.isEqn_diag_of_frame | exact GlobalTheory.FlagPush.isEqn_diag_of_frame | (intros; apply GlobalTheory.FlagPush.isEqn_diag_of_frame <;> assumption)
end

