import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussian
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevel
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (x : F) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 F, (r : F) = (m : F) * x :=
  _root_.UpperTheory.Reformulated.B.ExistsNatMulMem.exists_nat_mul_mem F x

theorem repr_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Af F) b).repr (inclR (Af F) x) k
      = algebraMap F (Af F) (b.repr x k) := by
  have h : inclR (Af F) x = (1 : Af F) ⊗ₜ[F] x := rfl
  rw [h, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem natCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_natCast]

theorem intCast_mul_eq_smul {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℤ) (z : E) :
    (n : E) * z = (n : F) • z := by
  rw [Algebra.smul_def, map_intCast]

theorem exists_clear_family {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {ι : Type} [Fintype ι] (e : ι → E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (t : ι) (o : 𝓞 E) (k : Fin d),
      ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (o : E))) k := by
  classical
  let B := RingOfIntegers.basis E
  choose m hm hr using fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d =>
    exists_nat_mul_mem F (b.repr (e p.1 * (B p.2.1 : E)) p.2.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun t o k => ?_⟩
  set D : ℕ := ∏ p, m p with hDdef
  have hterm : ∀ l, ∃ r : 𝓞 F, (r : F) = b.repr ((D : E) * (e t * (B l : E))) k := by
    intro l
    obtain ⟨c, hc⟩ : m (t, l, k) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨r, hr1⟩ := hr (t, l, k)
    refine ⟨(c : 𝓞 F) * r, ?_⟩
    rw [natCast_mul_eq_smul (F := F), map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    have hr2 : (r : F) = (m (t, l, k) : F) * b.repr (e t * (B l : E)) k := hr1
    change (c : F) * (r : F) = _
    rw [hr2]
    ring
  choose r hr' using hterm
  refine ⟨∑ l, (B.repr o l) • r l, ?_⟩
  have ho : (o : E) = ∑ l, ((B.repr o l : ℤ) : E) * (B l : E) := by
    have h3 := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
    rw [map_sum] at h3
    rw [show (o : E) = algebraMap (𝓞 E) E o from rfl, ← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  have hsum : (D : E) * (e t * (o : E))
      = ∑ l, ((B.repr o l : ℤ) : F) • ((D : E) * (e t * (B l : E))) := by
    rw [ho, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← intCast_mul_eq_smul]
    ring
  rw [hsum, map_sum, Finsupp.finsetSum_apply]
  have h4 : ((∑ l, (B.repr o l) • r l : 𝓞 F) : F) = ∑ l, ((B.repr o l : ℤ) : F) * (r l : F) := by
    rw [show ((∑ l, (B.repr o l) • r l : 𝓞 F) : F)
      = algebraMap (𝓞 F) F (∑ l, (B.repr o l) • r l) from rfl, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
  rw [h4]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hr']

theorem ratTuple_mem_latN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  intro F E _ _ _ _ _ d b M J n N hN
  obtain ⟨D, hD0, hD⟩ := exists_clear_family b (fun p : Fin M × Fin M => J⁻¹ p.1 p.2)
  refine ⟨N * D, Nat.mul_pos hN hD0, fun ρ => ?_⟩
  show ∀ a i, InNOh b N (ratTuple J (N * D) ρ a i)
  intro a j k
  choose r hr using fun i => hD (j, i) (ρ i a) k
  refine ⟨algebraMap F (Af F) (((∑ i, r i : 𝓞 F)) : F), ?_, ?_⟩
  · exact ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨_, rfl⟩
  · show (Algebra.TensorProduct.basis (Af F) b).repr
      (inclR (Af F) (((N * D : ℕ) : E) *
        (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)) k = _
    rw [repr_inclR]
    have h1 : ((N * D : ℕ) : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = (N : F) • ∑ i, (D : E) * (J⁻¹ j i * (ρ i a : E)) := by
      rw [← natCast_mul_eq_smul, Nat.cast_mul, Matrix.mulVec, dotProduct, ← Finset.mul_sum,
        mul_assoc]
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.finsetSum_apply,
      map_mul, map_natCast]
    congr 2
    rw [show ((∑ i, r i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ i, r i) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hr i).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RvRingPf

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem repr_one_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (bs.repr e k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem struct_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i j k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩

theorem one_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (k : Fin d) :
    algebraMap F (Fv F v) (bs.repr 1 k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem sig_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem repr_mul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (x * y) k =
      ∑ i, ∑ j, ((Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        (Algebra.TensorProduct.basis (Fv F v) bs).repr y j) *
          algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : x * y = ∑ i, ∑ j, (bK.repr x i * bK.repr y j) • ((1 : Fv F v) ⊗ₜ[F] (bs i * bs j)) := by
    conv_lhs => rw [← bK.sum_repr x, ← bK.sum_repr y]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hbK, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

theorem repr_sig (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (sigR (Fv F v) σ x) k =
      ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : sigR (Fv F v) σ x = ∑ i, bK.repr x i • ((1 : Fv F v) ⊗ₜ[F] σ (bs i)) := by
    conv_lhs => rw [← bK.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbK, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [sigR]
  rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

def ringOf {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) : Subring (Fv F v ⊗[F] E) where
  carrier := Rv bs v
  mul_mem' := by
    intro x y hx hy k
    rw [repr_mul]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (struct_int h i j k)
  one_mem' := by
    intro k
    rw [Algebra.TensorProduct.one_def, repr_one_tmul]
    exact one_int h k
  add_mem' := by
    intro x y hx hy k
    rw [map_add, Finsupp.add_apply]
    exact add_mem (hx k) (hy k)
  zero_mem' := by
    intro k
    rw [map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx k
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (hx k)

theorem sigR_mem {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (x : Fv F v ⊗[F] E) (hx : x ∈ ringOf h) :
    sigR (Fv F v) σ x ∈ ringOf h := by
  intro k
  rw [repr_sig]
  exact sum_mem fun i _ => mul_mem (hx i) (sig_int h i k)

theorem rvRing : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  intro F E _ _ _ _ _ σ d bs v h
  exact ⟨ringOf h, (sigR (Fv F v) σ).restrict (ringOf h) (ringOf h) (sigR_mem h), rfl, fun x => rfl⟩

end GlobalTheory.CompanionTheory.RvRingPf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelfDualVol
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.GunrVol

theorem selfDualVol : PositivityTheory.SiegelWeilFormula.Gunr.SelfDualVol := by
  intro V _ _ _ _ _ μ χ hsd L hLo hLc hadd _ hann
  obtain ⟨hH, hinv⟩ := hsd
  haveI := hH
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen L hLo
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hfin : μ (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hpos : μ (L : Set V) ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → ℂ, Φ = (L : Set V).indicator 1 := ⟨_, rfl⟩
  have hΦin : ∀ x ∈ L, Φ x = 1 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_mem (s := (L : Set V)) hx _
  have hΦout : ∀ x, x ∉ L → Φ x = 0 := fun x hx => by
    rw [hΦ]; exact Set.indicator_of_notMem (s := (L : Set V)) hx _
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_one.indicator (by
      intro a ha
      rw [(IsClopen.frontier_eq ⟨hLcl, hLo⟩)] at ha
      exact absurd ha (Set.notMem_empty a))
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc ?_
    intro x hx
    exact hΦout x hx
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (L : Set V) := ⟨_, rfl⟩
  have hI : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => (m : ℂ)) y := by
    intro y
    by_cases hy : y ∈ L
    · have h1 : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hann y).2 hy x hx, mul_one]
        · rw [hΦout x hx, zero_mul]
      rw [h1, Set.indicator_of_mem (s := (L : Set V)) hy, hΦ, integral_indicator hLm]
      simp [hm]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy]
      have h2 := (hann y).not.2 hy
      push_neg at h2
      obtain ⟨x0, hx0, hne⟩ := h2
      have h3 : ∫ x, Φ x * χ x y ∂μ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := by
        calc ∫ x, Φ x * χ x y ∂μ = ∫ x, (fun x => Φ x * χ x y) (x0 + x) ∂μ :=
              (integral_add_left_eq_self _ x0).symm
          _ = ∫ x, χ x0 y * (Φ x * χ x y) ∂μ := by
              congr 1
              funext x
              have : Φ (x0 + x) = Φ x := by
                by_cases hx : x ∈ L
                · rw [hΦin _ (L.add_mem hx0 hx), hΦin _ hx]
                · rw [hΦout _ (fun h => hx ((L.add_mem_cancel_left hx0).1 h)), hΦout _ hx]
              simp only [this, hadd]
              ring
          _ = χ x0 y * ∫ x, Φ x * χ x y ∂μ := integral_const_mul _ _
      have h4 : (1 - χ x0 y) * ∫ x, Φ x * χ x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← h3, sub_self]
      exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hInt : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [funext hI]
    exact (integrable_indicator_iff hLm).2 (integrableOn_const hfin)
  have h0 := hinv Φ hΦc hΦs hInt 0
  have hout : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = (L : Set V).indicator (fun _ => (m : ℂ)) := by
    funext y
    rw [hI]
    by_cases hy : y ∈ L
    · rw [(hann 0).2 L.zero_mem y hy, mul_one]
    · rw [Set.indicator_of_notMem (s := (L : Set V)) hy, zero_mul]
  rw [hout, integral_indicator hLm, neg_zero, hΦin 0 L.zero_mem] at h0
  have h5 : (m : ℂ) * m = 1 := by
    have := h0
    simp only [setIntegral_const, ← hm, Complex.real_smul] at this
    exact this
  have h6 : m * m = 1 := by exact_mod_cast h5
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  have h7 : m = 1 := by nlinarith
  rw [hm, measureReal_def, ENNReal.toReal_eq_one_iff] at h7
  exact h7

end GlobalTheory.CompanionTheory.GunrVol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShapeMemBounded
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F.F5

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinFamAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Cov (S : Set (Pre E n)) : Prop :=
  ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ S, ∃ j, PreEquiv (D j) D'

theorem cov_of_rel {S : Set (Pre E n)} {ι : Type*} [Finite ι] (P : ι → Pre E n → Prop)
    (h1 : ∀ D ∈ S, ∃ a, P a D)
    (h2 : ∀ a, ∀ D₁ ∈ S, ∀ D₂ ∈ S, P a D₁ → P a D₂ → PreEquiv D₁ D₂) : Cov S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨D₀, -⟩ := hS
    let e := Finite.equivFin ι
    refine ⟨Nat.card ι, fun j => if h : ∃ D ∈ S, P (e.symm j) D then h.choose else D₀, ?_⟩
    intro D' hD'
    obtain ⟨a, ha⟩ := h1 D' hD'
    have hex : ∃ D ∈ S, P (e.symm (e a)) D := ⟨D', hD', by rw [Equiv.symm_apply_apply]; exact ha⟩
    refine ⟨e a, ?_⟩
    show PreEquiv (if h : ∃ D ∈ S, P (e.symm (e a)) D then h.choose else D₀) D'
    rw [dif_pos hex]
    obtain ⟨hmem, hP⟩ := hex.choose_spec
    exact h2 _ _ hmem _ hD' hP (by rw [Equiv.symm_apply_apply]; exact ha)
  · exact ⟨0, Fin.elim0, fun D' hD' => (hS ⟨D', hD'⟩).elim⟩

theorem cov_of_cover {S : Set (Pre E n)} {ι : Type*} [Finite ι] (A : ι → Set (Pre E n))
    (hA : ∀ a, Cov (A a)) (hS : ∀ D ∈ S, ∃ a, D ∈ A a) : Cov S := by
  classical
  choose k D hD using fun a => (hA a : ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ A a, ∃ j, PreEquiv (D j) D')
  let e := Finite.equivFin (Σ a, Fin (k a))
  refine ⟨Nat.card (Σ a, Fin (k a)), fun j => D (e.symm j).1 (e.symm j).2, ?_⟩
  intro D' hD'
  obtain ⟨a, ha⟩ := hS D' hD'
  obtain ⟨j, hj⟩ := hD a D' ha
  refine ⟨e ⟨a, j⟩, ?_⟩
  show PreEquiv (D (e.symm (e ⟨a, j⟩)).1 (e.symm (e ⟨a, j⟩)).2) D'
  rw [Equiv.symm_apply_apply]
  exact hj

abbrev Shape (E : Type) [Field E] : Type :=
  Σ c : ℕ, (Fin c → ℕ) × (Fin c → (E →+* ℂ) → Multiset ℂ)

def shape (D : Pre E n) : Shape E := ⟨D.c, D.N, D.m⟩

def bounded (E : Type) [Field E] (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : Set (Shape E) :=
  {t | t.1 ≤ n ∧ (∀ i, t.2.1 i ≤ n) ∧ ∀ i τ, t.2.2 i τ ≤ m τ}

theorem finite_le (s : Multiset ℂ) : {x : Multiset ℂ | x ≤ s}.Finite := by
  exact (Multiset.finite_toSet s.powerset).subset fun x hx => Multiset.mem_powerset.mpr hx

theorem bounded_finite (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : (bounded E n m).Finite := by
  refine ((Set.finite_Iic n).biUnion fun c _ =>
    (((Set.Finite.pi fun _ : Fin c => Set.finite_Iic n).prod
      (Set.Finite.pi fun _ : Fin c => Set.Finite.pi fun τ => finite_le (m τ))).image
        (fun p => (⟨c, p⟩ : Shape E)))).subset ?_
  rintro ⟨c, N, mm⟩ ⟨hc, hN, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨(N, mm), ⟨fun i _ => hN i, fun i _ τ _ => hm i τ⟩, rfl⟩⟩

theorem shape_mem_bounded (m : (E →+* ℂ) → Multiset ℂ) (D : Pre E n)
    (hm : ∀ τ, ∑ i, D.m i τ = m τ) : shape D ∈ bounded E n m := by
  refine ⟨?_, fun i => ?_, fun i τ => ?_⟩
  · show D.c ≤ n
    calc D.c = ∑ _i : Fin D.c, 1 := by simp
      _ ≤ ∑ i, D.N i := Finset.sum_le_sum fun i _ => D.pos i
      _ = n := D.h
  · show D.N i ≤ n
    exact (Finset.single_le_sum (f := D.N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
  · show D.m i τ ≤ m τ
    rw [← hm τ]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun j _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem cov_fibre (hL : LevelFactor) (hF : FinDiscN)
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (hK : IsLevel K) (hW : ∀ N, FiniteDimensional ℂ (W N))
    (t : Shape E) :
    Cov {D' : Pre E n | shape D' = t ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
  classical
  obtain ⟨c, N, mm⟩ := t
  by_cases hsum : ∑ i, N i = n
  swap
  · refine ⟨0, Fin.elim0, ?_⟩
    rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, -, -⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (eq_of_heq hh)
    exact absurd h' hsum
  choose Ki hKiopen hKiKGL hKisph using fun w => hL E w c n N hsum (K w) (hK.1 w)
  have hlev : ∀ i : Fin c, IsLevel (fun w => Ki w i) := fun i =>
    ⟨fun w => hKiopen w i, hK.2.mono fun w hw => hKiKGL w hw i⟩
  choose k σs hσs using fun i : Fin c =>
    hF E (N i) (fun w => Ki w i) (W (N i)) (mm i) (hlev i) (hW (N i))
  refine cov_of_rel (ι := (i : Fin c) → Fin (k i))
    (fun a D => ∃ hc : D.c = c, ∀ (i : Fin D.c) w, ∃ hs hi,
      D.cls i w = GlobalTheory.LocGL.IrrGL.of (σs (Fin.cast hc i) (a (Fin.cast hc i)) w).ρ hs hi) ?_ ?_
  · rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, hsph, hKt⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
    choose a ha using fun i => hσs i (V' i) (fun w => σ' i w) (disc' i) (fun w => loc' i w)
      (fun τ => inf' i τ) (fun w => hKisph w (fun j => σ' j w) (hsph w) i) (hKt i)
    exact ⟨a, rfl, fun i w => ⟨_, _, (ha i w).symm⟩⟩
  · rintro a ⟨c₁, N₁, h₁, V₁, σ₁, m₁, pos₁, disc₁, loc₁, inf₁⟩ ⟨hsh₁, -, -⟩
      ⟨c₂, N₂, h₂, V₂, σ₂, m₂, pos₂, disc₂, loc₂, inf₂⟩ ⟨hsh₂, -, -⟩ ⟨hc₁, hP₁⟩ ⟨hc₂, hP₂⟩
    obtain ⟨rfl, hh₁⟩ := Sigma.mk.inj_iff.mp hsh₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₁)
    obtain ⟨rfl, hh₂⟩ := Sigma.mk.inj_iff.mp hsh₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₂)
    refine ⟨finCongr rfl, fun i w => ?_, fun i τ => rfl⟩
    obtain ⟨hs₁, hi₁, e₁⟩ := hP₁ i w
    obtain ⟨hs₂, hi₂, e₂⟩ := hP₂ i w
    exact e₁.trans e₂.symm

theorem finFamOf : FinFamOf := by
  intro hL hF E _ _ _ n K W m hK hW
  have hS : Cov {D' : Pre E n | (∀ τ, ∑ i, D'.m i τ = m τ) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
    have hfin := bounded_finite (E := E) n m
    haveI := hfin.to_subtype
    refine cov_of_cover (ι := bounded E n m) (fun t => {D' : Pre E n | shape D' = t.1 ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)}) (fun t => cov_fibre hL hF K W hK hW t.1) ?_
    rintro D' ⟨hm, hsph, hKt⟩
    exact ⟨⟨shape D', shape_mem_bounded m D' hm⟩, rfl, hsph, hKt⟩
  obtain ⟨k, D, hD⟩ := hS
  exact ⟨k, D, fun D' hm hsph hKt => hD D' ⟨hm, hsph, hKt⟩⟩

end GlobalTheory.CompanionTheory.FinFamAssembly

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussianStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_fourier_gaussian : Ad3.R.B0 → Ad3.R.FT := by
  first | exact @GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts | exact GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts | (intros; apply GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualDenominatorBoundedStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dual_denominator_bounded : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer | exact GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer <;> assumption)
end

