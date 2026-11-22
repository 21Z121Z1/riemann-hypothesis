import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersAction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BalProjOpen

open GlobalTheory.BalProj

theorem eigSp_eq_range {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (P : Matrix (Fin n) (Fin n) k) (hP : ∀ a, P * B a = χ a • P) (hfix : ∀ c ∈ eigSp B χ, c ᵥ* P = c) :
    eigSp B χ = LinearMap.range (Matrix.vecMulLinear P) := by
  ext c
  constructor
  · intro hc
    exact ⟨c, hfix c hc⟩
  · rintro ⟨d, rfl⟩ a
    show (d ᵥ* P) ᵥ* B a = χ a • (d ᵥ* P)
    rw [Matrix.vecMul_vecMul, hP a, Matrix.vecMul_smul]

theorem finrank_range_eq_trace {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hP : P * P = P) :
    (Module.finrank k (LinearMap.range (Matrix.vecMulLinear P)) : k) = P.trace := by
  have h1 : Matrix.vecMulLinear P = Matrix.toLin' Pᵀ := by
    ext c i
    simp [Matrix.mulVec_transpose]
  have hi : IsIdempotentElem (Matrix.toLin' Pᵀ) := by
    show Matrix.toLin' Pᵀ * Matrix.toLin' Pᵀ = Matrix.toLin' Pᵀ
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.transpose_mul, hP]
  rw [h1, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq, Matrix.trace_transpose]

theorem eigRank_cast_eq_trace {O R k : Type} [CommRing O] [CommRing R] [Field k] (φ : R →+* k) {n : ℕ}
    (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) :
    (eigRank φ A χ : k) = φ (∑ i, f i • A (b i)).trace := by
  set P := ∑ i, f i • A (b i) with hPdef
  have hPA : ∀ a, P * A a = χ a • P := by
    intro a
    rw [← h2 a, hPdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← hmul, mul_comm]
  have hPP : P * P = P := by
    conv_lhs => arg 2; rw [hPdef]
    rw [Finset.mul_sum]
    simp_rw [mul_smul_comm, hPA, smul_smul, ← Finset.sum_smul, h1, one_smul]
  set Pb := P.map φ
  have hPbA : ∀ a, Pb * (A a).map φ = φ (χ a) • Pb := by
    intro a
    rw [← Matrix.map_mul, hPA a]
    ext i j
    simp [Pb]
  have hfix : ∀ c ∈ eigSp (fun a => (A a).map φ) (fun a => φ (χ a)), c ᵥ* Pb = c := by
    intro c hc
    have : Pb = ∑ i, φ (f i) • (A (b i)).map φ := by
      ext i j
      simp [Pb, hPdef, Matrix.sum_apply, map_sum]
    rw [this, Matrix.vecMul_sum]
    simp_rw [Matrix.vecMul_smul, hc _, smul_smul, ← Finset.sum_smul, ← map_mul, ← map_sum, h1, map_one, one_smul]
  have hPbPb : Pb * Pb = Pb := by rw [← Matrix.map_mul, hPP]
  unfold eigRank
  rw [eigSp_eq_range _ _ Pb hPbA hfix, finrank_range_eq_trace Pb hPbPb]
  simp [Pb, Matrix.trace, map_sum]

theorem isOpen_eigRank_eq_of_datum {O R K : Type} [CommRing O] [CommRing R] [Field K] [CharZero K] (j : K →+* R)
    {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R) (hmul : ∀ a b, A (a * b) = A a * A b) (χ : O → R)
    {J : Type} [Fintype J] (f : J → R) (b : J → O) (h1 : ∑ i, f i * χ (b i) = 1)
    (h2 : ∀ a, ∑ i, f i • A (a * b i) = χ a • ∑ i, f i • A (b i)) (N : ℕ) :
    IsOpen {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} := by
  set t := (∑ i, f i • A (b i)).trace with ht
  have key : ∀ (𝔭 : PrimeSpectrum R) (M : ℕ),
      eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = M ↔ t - M ∈ 𝔭.asIdeal := by
    intro 𝔭 M
    haveI : CharZero 𝔭.asIdeal.ResidueField :=
      (RingHom.charZero_iff ((algebraMap R 𝔭.asIdeal.ResidueField).comp j).injective).1 inferInstance
    rw [← Nat.cast_inj (R := 𝔭.asIdeal.ResidueField), eigRank_cast_eq_trace _ A hmul χ f b h1 h2,
      ← Ideal.algebraMap_residueField_eq_zero, map_sub, map_natCast, sub_eq_zero]
  have hle : ∀ 𝔭 : PrimeSpectrum R, eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ ≤ n := by
    intro 𝔭
    unfold eigRank
    exact (Submodule.finrank_le _).trans (by simp)
  have hset : {𝔭 : PrimeSpectrum R | eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A χ = N} =
      (⋃ M ∈ (Finset.range (n + 1)).filter (· ≠ N), PrimeSpectrum.zeroLocus {t - (M : R)})ᶜ := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, exists_prop, not_exists, not_and]
    constructor
    · intro h M hM hM'
      exact hM.2 (((key 𝔭 M).2 hM').symm.trans h)
    · intro h
      by_contra hne
      exact h _ ⟨Nat.lt_succ_of_le (hle 𝔭), hne⟩ ((key 𝔭 _).1 rfl)
  rw [hset]
  exact (isClosed_biUnion_finset fun M _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

theorem exists_datum {E : Type} [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ)
    (A : 𝓞 E → Matrix (Fin n) (Fin n) R) (hadd : ∀ a b, A (a + b) = A a + A b) (τ : E →+* ℂ) :
    ∃ (J : Type) (_ : Fintype J) (f : J → R) (b : J → 𝓞 E),
      ∑ i, f i * embR F hF iF τ (b i) = 1 ∧
      ∀ a, ∑ i, f i • A (a * b i) = embR F hF iF τ a • ∑ i, f i • A (b i) := by
  classical
  set bO := RingOfIntegers.basis E
  set bE := integralBasis E
  have hnd := _root_.traceForm_nondegenerate ℚ E
  obtain ⟨d, hd⟩ : ∃ d, d = (Algebra.traceForm ℚ E).dualBasis hnd bE := ⟨_, rfl⟩
  have hdr : ∀ i j, Algebra.trace ℚ E (bE i * d j) = if i = j then 1 else 0 := by
    intro i j
    rw [← Algebra.traceForm_apply, hd]
    exact LinearMap.BilinForm.apply_dualBasis_right hnd (Algebra.traceForm_isSymm ℚ) bE i j
  have hdrep0 : ∀ (y : E) i, d.repr y i = Algebra.trace ℚ E (y * bE i) := by
    intro y i
    rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  set g : E →+* R := iF.comp (τ.codRestrict F.toSubfield (hF τ))
  have hg : ∀ a : 𝓞 E, embR F hF iF τ a = g (a : E) := fun a => rfl
  have hbE : ∀ i, bE i = (bO i : E) := fun i => integralBasis_apply E i
  have hrep : ∀ (y : E) i, bE.repr y i = Algebra.trace ℚ E (y * d i) := by
    intro y i
    conv_rhs => rw [← bE.sum_repr y]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, hdr, smul_eq_mul, mul_ite, _root_.mul_one]
    simp
  have hdrep : ∀ y : E, y = ∑ i, Algebra.trace ℚ E (y * bE i) • d i := by
    intro y
    conv_lhs => rw [← d.sum_repr y]
    simp_rw [hdrep0]
  have hA : ∑ i, d i * bE i = 1 := by
    rw [← sub_eq_zero]
    refine hnd.1 _ fun y => ?_
    rw [Algebra.traceForm_apply, sub_mul, map_sub, _root_.one_mul, Finset.sum_mul, map_sum, sub_eq_zero,
      Algebra.trace_eq_matrix_trace bE y, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep]
    congr 1
    ring
  have hB : ∀ (a : 𝓞 E) j, ∑ i, ((bO.repr (a * bO i) j : ℤ) : E) * d i = (a : E) * d j := by
    intro a j
    conv_rhs => rw [hdrep ((a : E) * d j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Algebra.trace ℚ E ((a : E) * d j * bE i) = bE.repr ((a : E) * bE i) j := by
      rw [hrep]; congr 1; ring
    have h2 : bE.repr ((a : E) * bE i) j = ((bO.repr (a * bO i) j : ℤ) : ℚ) := by
      rw [hbE]
      exact integralBasis_repr_apply E (a * bO i) j
    rw [h1, h2, Algebra.smul_def, eq_ratCast, Rat.cast_intCast]
  have hexp : ∀ x : 𝓞 E, A x = ∑ j, bO.repr x j • A (bO j) := by
    intro x
    let Aa : 𝓞 E →+ Matrix (Fin n) (Fin n) R := AddMonoidHom.mk' A hadd
    conv_lhs => rw [← bO.sum_repr x]
    exact (map_sum Aa _ _).trans (Finset.sum_congr rfl fun j _ => map_zsmul Aa _ _)
  refine ⟨_, inferInstance, fun i => g (d i), bO, ?_, ?_⟩
  · simp_rw [hg, ← map_mul, ← map_sum, ← hbE, hA, map_one]
  · intro a
    calc ∑ i, g (d i) • A (a * bO i)
        = ∑ i, ∑ j, (g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexp (a * bO i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_smul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, g (d i) * ((bO.repr (a * bO i) j : ℤ) : R)) • A (bO j) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = ∑ j, (embR F hF iF τ a * g (d j)) • A (bO j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [hg, ← map_mul, ← hB a j, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul g, map_intCast g, _root_.mul_comm]
      _ = _ := by
          rw [Finset.smul_sum]
          simp_rw [smul_smul]

theorem isOpen_eigRank_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  intro E _ _ _ F hF R _ iF n A h1 hadd hmul τ N
  obtain ⟨J, _, f, b, hf1, hf2⟩ := exists_datum F hF R iF n A hadd τ
  exact isOpen_eigRank_eq_of_datum iF A hmul _ f b hf1 hf2 N

end GlobalTheory.BalProjOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatioTwoMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatRatio.Square

variable {R : Type} [CommRing R] [IsDomain R]

theorem famφB_zero_one (Q : DegPre R) : Q.famφB 0 1 = 𝟙 _ := by
  show (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c 0)).left = 𝟙 _
  rw [GlobalTheory.Mum.degPre_c_zero, padd, comp_one, ← Hom.mul_def, _root_.mul_one]
  rfl

theorem famφB_zero_two (Q : DegPre R) : Q.famφB 0 2 = Q.famφB 0 3 := by
  show (toUnit Q.P.A ≫ Q.c 0).left = (toUnit Q.P.A ≫ η[Q.P.A]).left
  rw [GlobalTheory.Mum.degPre_c_zero, comp_one, Hom.one_def]

theorem formEq (Q : DegPre R) (N : ℕ) :
    FormEq (Sum.elim (Q.famφB 0) (Q.famφB 0)) (Sum.elim (DegPre.famε N) (DegPre.famε N))
      (Q.famφB 0) (DegPre.famε (2 * N)) := by
  intro U _ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four]
  have e1 := famφB_zero_one Q
  have e2 := famφB_zero_two Q
  have e0 : Q.famφB 0 0 = 𝟙 _ := rfl
  rw [e1, e2, e0]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize h (𝟙 _) = a
  generalize h (Q.famφB 0 3) = b
  push_cast
  have hs : ∀ k : ℤ, a ^ (k - 1) * a ^ (1 : ℤ) = a ^ k := fun k => by rw [← zpow_add, sub_add_cancel]
  rw [hs, hs, zpow_neg_one, zpow_one, inv_mul_cancel_right, inv_mul_cancel_right, ← zpow_add, two_mul]

theorem isRatio_two_mul (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens)
    (f : Γ(Q.P.A.left, U)) (_hN : 1 ≤ N) (h : GlobalTheory.HeatRatio.IsRatio Q σ σ' U f) :
    ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f := by
  obtain ⟨ρ, hρ⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ σ')
  obtain ⟨ρ', hρ'⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ' σ')
  refine ⟨ρ, ρ', fun z hz J hJ => ?_⟩
  obtain ⟨hu, he⟩ := h z hz J hJ
  rw [hρ _ _ z J hJ, hρ' _ _ z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, he]
  exact ⟨hu.mul hu, by ring⟩

end GlobalTheory.HeatRatio.Square

theorem GlobalTheory.HeatRatio.isRatio_square : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), 1 ≤ N → GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f :=
  fun _ _ _ Q N σ σ' U f hN h => GlobalTheory.HeatRatio.Square.isRatio_two_mul Q N σ σ' U f hN h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermOfIsWeightStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_of_isWeight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  first | exact @GlobalTheory.Heat.isTerm_of_isWt | exact GlobalTheory.Heat.isTerm_of_isWt | (intros; apply GlobalTheory.Heat.isTerm_of_isWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatTermLin

theorem gs_sub_fn {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem sval_sub_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s t : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (s - c • t) r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  have hm := hJ.mem φ r
  have h1 : sval (s - c • t) r z J = sval s r z J - sval (c • t) r z J :=
    gs_sub_fn r z _ hm _ _
  have h2 : sval (c • t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  rw [h1, h2]

theorem gs_constFn {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (e : R) :
    gs r z ⊤ (constFn p ⊤ e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← gs_pull r p z ⊤ trivial]
  exact gs_res r z (U := p ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _

theorem isTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ σ' τ τ' e h h' T x y J hJ
  have a := sval_sub_smul (constFn Y.H.hom ⊤ e) τ' τ x.left y hJ
  have b := sval_sub_smul (constFn Q.P.A.hom ⊤ e) σ' σ (x ≫ Y.q).left y hJ
  rw [gs_constFn, Over.w] at a b
  refine a.trans ?_
  rw [h T x y J hJ, h' T x y J hJ]
  refine Eq.trans ?_ (congrArg (· * _) b).symm
  ring

end GlobalTheory.HeatTermLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  first | exact @GlobalTheory.Heat.IsInv.isWt | exact GlobalTheory.Heat.IsInv.isWt | (intros; apply GlobalTheory.Heat.IsInv.isWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtMul

open GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_add {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hq : x' ≫ Y.q = x ≫ Y.q)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J)
    (χ χ' : Q.X) : c (χ + χ') = c χ * c χ' := by
  have hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ') := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e₁ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'
    have e₂ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'
    rw [Ray.Φ_b] at e₁ e₂
    rw [hq] at e₂
    dsimp only [GlobalTheory.TorusModel.cv] at e₁ e₂
    rw [hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm] at e₂
    rw [map_mul]
    exact mul_right_cancel e₂
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this
  refine Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))
  exact congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)

theorem isWt_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  intro R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]
  ring

end GlobalTheory.Heat.WtMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpensStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  first | exact @GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | exact GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | (intros; apply GlobalTheory.Heat.WtLocal.isWt_of_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionSubConstMul
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem valR_sub_const_mul {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp R) (φ : R →+* S)
    (x : Sp S ⟶ X) (hx : x ≫ p = spMap φ) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(X, W)) (r : R) :
    valR x W (f - constFn p W r * g) = valR x W f - φ r * valR x W g := by
  have hc : valR x W (constFn p W r) = φ r := GlobalTheory.Points.valR_constFn_of_over p φ x hx W h r
  rw [← hc]
  unfold valR
  simp only [dif_pos h, map_sub, map_mul]

theorem isWt_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  intro R _ _ Q Ω _ _ _ oa Y α W f g r hf hg S _ φ x x' c a a' ha ha' hW hW' hq hc
  have h1 := hf S φ x x' c a a' ha ha' hW hW' hq hc
  have h2 := hg S φ x x' c a a' ha ha' hW hW' hq hc
  have e : a ≫ Y.H.hom = spMap φ := by rw [ha]; exact Over.w x
  have e' : a' ≫ Y.H.hom = spMap φ := by rw [ha']; exact Over.w x'
  rw [valR_sub_const_mul _ φ a e W hW, valR_sub_const_mul _ φ a' e' W hW', h1, h2]
  ring

end GlobalTheory.HeatMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberWeightSetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_number_weight_set : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  first | exact @GlobalTheory.JetsCst.jets_cst | exact GlobalTheory.JetsCst.jets_cst | (intros; apply GlobalTheory.JetsCst.jets_cst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdealStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivatives_coboundary_coeffs_mem_maximalIdeal : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := by
  first | exact @GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob | exact GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob | (intros; apply GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k), (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧ (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) := by
  first | exact @GlobalTheory.Dieu.isog_basics | exact GlobalTheory.Dieu.isog_basics | (intros; apply GlobalTheory.Dieu.isog_basics <;> assumption)
end

