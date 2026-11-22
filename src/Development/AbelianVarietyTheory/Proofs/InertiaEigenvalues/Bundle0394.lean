import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import GroundTheory.LocalFields.KroneckerWeber
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem polyDelta_supported_linear_mod (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ) :
    ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧
      ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i),
        (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  intro s hs
  have hX : ∀ (U : Set ℕ) (j : ℕ), j ∈ U → (MvPolynomial.X j : MvPolynomial ℕ A) ∈ MvPolynomial.supported A U :=
    fun U j hj => by
      rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨j, hj, rfl⟩
  have hC : ∀ (U : Subalgebra A (MvPolynomial ℕ A)) (a : A), MvPolynomial.C a ∈ U :=
    fun U a => U.algebraMap_mem a
  set S := MvPolynomial.supported A (Set.Iic i) with hS
  set T := MvPolynomial.supported A (Set.Iic (i + 1)) with hT
  have hST : S ≤ T := MvPolynomial.supported_mono (Set.Iic_subset_Iic.2 (Nat.le_succ i))
  have hcc : ∀ x y, x ∈ S → y ∈ S → cc l x y ∈ S := by
    intro x y hx hy
    unfold cc
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.pow_mem _ hx _))
      (Subalgebra.pow_mem _ hy _)
  have hS' : S = Algebra.adjoin A (MvPolynomial.X '' Set.Iic i) := MvPolynomial.supported_eq_adjoin_X _
  rw [hS'] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j ≤ i := Set.mem_Iic.1 hj
    rw [polyDelta_X]
    refine ⟨hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
    rcases Nat.lt_or_ge j i with h | h
    · refine ⟨0, Subalgebra.zero_mem _, MvPolynomial.X (j + 1), hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
      simp
    · have : j = i := le_antisymm hj' h
      subst this
      refine ⟨1, Subalgebra.one_mem _, 0, Subalgebra.zero_mem _, ?_⟩
      simp
  | algebraMap a =>
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨hC _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ a), hC _ _, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x + y) = (polyDelta D).δ x + (polyDelta D).δ y - cc l x y := (polyDelta D).δ_add x y
    rw [hd]
    refine ⟨T.sub_mem (T.add_mem hx1 hy1) (hST (hcc x y hx hy)), a1 + a2, S.add_mem ha1 ha2,
      b1 + b2 - cc l x y, S.sub_mem (S.add_mem hb1 hb2) (hcc x y hx hy), ?_⟩
    have := Ideal.add_mem _ hx2 hy2
    convert this using 1
    ring
  | mul x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x * y) = x ^ l * (polyDelta D).δ y + y ^ l * (polyDelta D).δ x +
        (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y := (polyDelta D).δ_mul x y
    rw [hd]
    refine ⟨T.add_mem (T.add_mem (T.mul_mem (T.pow_mem (hST hx) _) hy1) (T.mul_mem (T.pow_mem (hST hy) _) hx1))
        (T.mul_mem (T.mul_mem (T.natCast_mem _) hx1) hy1),
      x ^ l * a2 + y ^ l * a1, S.add_mem (S.mul_mem (S.pow_mem hx _) ha2) (S.mul_mem (S.pow_mem hy _) ha1),
      x ^ l * b2 + y ^ l * b1, S.add_mem (S.mul_mem (S.pow_mem hx _) hb2) (S.mul_mem (S.pow_mem hy _) hb1), ?_⟩
    have h3 : (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y ∈
        Ideal.span {(l : MvPolynomial ℕ A)} :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (x ^ l) hy2) (Ideal.mul_mem_left _ (y ^ l) hx2)) h3
    convert this using 1
    ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
section
noncomputable section

namespace GlobalTheory.InvJump

section Generic

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem eq_zero_of_mem_Fil_one (c : K) (h : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this
  exact PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h1 PD.mem_filtration_one)

theorem isJumpV_zero_of_invariant [CharZero Qp] (ρ : Representation LL G V) (x : V) (hx : x ≠ 0)
    (hinv : ∀ g, ρ g x = x) (τ : K →ₐ[Qp] LL) : IsJumpV PD ρ τ 0 := by
  classical
  haveI := PD.finK
  let b := Module.finBasis Qp K
  let b' := b.traceDual
  let y : V ⊗[Qp] BdR := ∑ i, (τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b i)
  have e1 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b' j) • b j := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b.sum_repr z, Finset.sum_mul, map_sum]
    simp only [b', smul_mul_assoc, map_smul, Module.Basis.trace_mul_traceDual]
    simp
  have e2 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b j) • b' j := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b'.sum_repr z]
    simp [b', Finset.sum_mul, Module.Basis.trace_traceDual_mul]
  have h0 : y ∈ FildR PD ρ τ 0 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      simp [y, actVdR, map_sum, hinv]
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
      intro c
      have l : mulVdR (LL := LL) (V := V) c y =
          ∑ i, ∑ j, Algebra.trace Qp K (c * b i * b' j) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, map_sum, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          LinearMap.mulLeft_apply, ← map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [e1 (c * b i), map_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← tmul_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      have r : τ c • y =
          ∑ j, ∑ i, Algebra.trace Qp K (c * b' j * b i) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, Finset.smul_sum, smul_tmul', smul_smul, ← map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [e2 (c * b' j), map_sum, Finset.sum_smul, sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_assoc]
      rw [l, r, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm]
    · refine Submodule.sum_mem _ fun i _ => ⟨(τ (b' i) • x) ⊗ₜ ⟨algebraMap K BdR (b i), ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  intro h
  rw [← h] at h0
  obtain ⟨w, hw⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[LL] LL, f x = 1 := Module.Projective.exists_dual_eq_one LL hx
  let m : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (φ ∘ₗ f.restrictScalars Qp).rTensor BdR
  have hm : ∀ w, m (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype w) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ (f v)) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have h1 := hm w
  rw [hw] at h1
  have h2 : m y = algebraMap K BdR (∑ i, φ (τ (b' i)) • b i) := by
    simp only [y, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [m, hf, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [h2] at h1
  have h3 := eq_zero_of_mem_Fil_one PD _ (by rw [zero_add] at h1; exact h1)
  have h4 : ∀ i, φ (τ (b' i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
  have h5 : φ ∘ₗ τ.toLinearMap = 0 := b'.ext fun i => by simpa using h4 i
  have := LinearMap.congr_fun h5 1
  simp [hφ] at this

end Generic

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

open scoped Pointwise in

theorem noInv_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  intro D bkP i s hJ v hv A hA x hx
  by_contra hx0
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) (D.nd.plOm.2 v) hA
  let Bw := bkP.br i v hv
  have inj : Function.Injective Bw.toLL := Subtype.val_injective.comp Bw.eO.injective
  let ψ : FractionRing (D.ntw.O0 i) →+* ↥Bw.LL.1 := IsFractionRing.lift inj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap inj a
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) ↥Bw.LL.1 := fun g => (Tmat i s g).map Bw.toLL
  have hM : ∀ g g', M (g * g') = M g * M g' := fun g g' => by
    simp only [M, ← Tgl_coe, map_mul, Units.val_mul, Matrix.map_mul]
  have hM1 : M 1 = 1 := by
    simp only [M, ← Tgl_coe, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let z : Fin D.R.r → ↥Bw.LL.1 := fun a => ψ (x a)
  have hz : ∀ g ∈ Dec (F := D.host.E) A, (M g).mulVec z = z := fun g hg => by
    funext a
    have := congrArg ψ (congrFun (hx g hg) a)
    simpa [Matrix.mulVec, dotProduct, map_sum, hψ, M, z] using this
  have hz0 : (M k⁻¹).mulVec z ≠ 0 := fun h => hx0 (by
    have h1 := congrArg (M k).mulVec h
    rw [Matrix.mulVec_mulVec, ← hM, mul_inv_cancel, hM1, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    funext a
    exact ψ.injective (by simpa [z] using congrFun h1 a))
  let τ : EmbV bkP i v hv := Bw.Kw.1.val.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split Bw.Kw.1.val)
  have hj := isJumpV_zero_of_invariant (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) _ hz0 (fun g => by
    have hg : k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹ ∈ Dec (F := D.host.E) A := by
      have h : (Bw.e.symm g : Gen.GE D.nd) • D.nd.plOm.1 v = D.nd.plOm.1 v := (Bw.e.symm g).2
      show (k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹) • A = A
      rw [← hk, mul_smul, inv_smul_smul, mul_smul, h]
    have e : repV bkP i v hv (Tgl i s) g ((M k⁻¹).mulVec z) =
        (M (Bw.e.symm g : Gen.GE D.nd)).mulVec ((M k⁻¹).mulVec z) := by
      simp only [M, ← Tgl_coe]
      rfl
    rw [e]
    conv_rhs => rw [← hz _ hg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ← hM, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel, one_mul]) τ
  have := hJ v hv τ 0 hj
  omega

end GlobalTheory.InvJump

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NoJumpMult

open Module TensorProduct

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  have h := PD.Fil_anti a
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  have : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
          (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from h))) := by
    ext x y; rfl
  rw [this]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a ≤ Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (hpos : 0 < finrank LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ))
    (hj : Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : Formalism.WeaklyAdmissibleFiltrations.multV PD ρ τ a ≠ 0 := by
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)
  have hlt : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) < Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) hj
  have := Submodule.finrank_lt_finrank_of_lt hlt
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega
end Gen

end GlobalTheory.NoJumpMult

namespace GlobalTheory.NoJumpMult

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  unfold Formalism.BasicNotions.Ranks.r; omega

theorem noJump_of_jumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  intro D bkP i s ι J hH hJ hG v hv τ a ha
  obtain ⟨τc, hτc, -⟩ := GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
  have hdR := (hH v hv (Tgl i s) (Set.mem_insert_of_mem _ rfl)).1
  have hK : 0 < Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 := by
    have := (bkP.br i v hv).Kw.2
    exact Module.finrank_pos
  have hpos : 0 < Module.finrank ↥(bkP.br i v hv).LL.1
      ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) := by
    have : Module.finrank ↥(bkP.br i v hv).LL.1
      ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) =
        Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 * D.R.r := hdR
    rw [this]; exact Nat.mul_pos hK (r_pos D)
  have hm := multV_ne_zero _ _ τ a hpos ha
  rw [hJ v hv τ τc hτc a] at hm
  have hmem : a ∈ J τc := by
    by_contra hn
    exact hm (by simp [Multiset.count_eq_zero.mpr hn])
  exact (hG τc).2.2 a hmem

end GlobalTheory.NoJumpMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInvDual_of_setup_of_isDual_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  first | exact @GlobalTheory.NewPrime.noInvDual_of_setup | exact GlobalTheory.NewPrime.noInvDual_of_setup | (intros; apply GlobalTheory.NewPrime.noInvDual_of_setup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmallStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  first | exact @GlobalTheory.BSP.norm_toDisc_J_pow_small | exact GlobalTheory.BSP.norm_toDisc_J_pow_small | (intros; apply GlobalTheory.BSP.norm_toDisc_J_pow_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrdIsEqCardInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_equivariant_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  first | exact @GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | exact GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | (intros; apply GlobalTheory.NewPrime.PairEquiv.pairing_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_finite_module_rows_criterion : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n), Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A), (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  first | exact @GlobalTheory.NewPrime.charDual_cogenerator | exact GlobalTheory.NewPrime.charDual_cogenerator | (intros; apply GlobalTheory.NewPrime.charDual_cogenerator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariantsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRingCore_crystalline_deRham_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvB ∧ C.InvdR := by
  first | exact @GlobalTheory.MemLoc.fits_inv | exact GlobalTheory.MemLoc.fits_inv | (intros; apply GlobalTheory.MemLoc.fits_inv <;> assumption)
end

