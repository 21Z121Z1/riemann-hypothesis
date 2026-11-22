import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0686
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsionStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_lower_bound_torsion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariantStatement
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
theorem _root_.GlobalTheory.T.delta_conj_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E), delta (c.map σ) = delta c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaPosIndexStatement
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
theorem _root_.GlobalTheory.T.delta_ne_zero' : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOrderBoundedHeckeSupport
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem det_mem_Ov {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} (hM : IsInt w M) : M.det ∈ Ov E w := by
  have hN : M = (Ov E w).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : Ov E w)) := by
    ext i j; rfl
  rw [hN, ← RingHom.map_det]
  exact SetLike.coe_mem _

private theorem v_eq_ofAdd_lemma {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (x : w.adicCompletion E) (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dif_neg h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem ordL_det_range : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  intro E _ _ w n ϖ hϖ g hg hgi
  have hd : g.val.det ∈ Ov E w := det_mem_Ov hg
  have hdi : (ϖ • (g⁻¹).val).det ∈ Ov E w := det_mem_Ov hgi
  have hmul : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hd0 : g.val.det ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hdi0 : (g⁻¹).val.det ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [Matrix.det_smul, Fintype.card_fin] at hdi
  simp only [Ov, ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers] at hd hdi
  rw [map_mul, map_pow, show Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from hϖ,
    v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le,
    nsmul_eq_mul, mul_neg, mul_one] at hdi
  rw [v_eq_ofAdd_lemma _ hd0, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at hd
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one, v_eq_ofAdd_lemma _ hd0, v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_mul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at hm
  refine ⟨(ordL g.val.det).toNat, ?_, ?_⟩
  · omega
  · omega

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalLatticeIndexPow
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.LatDiag

variable {E : Type} [Field E] [NumberField E] {w : Pl E}

theorem unif_ne_zero {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  rintro rfl
  unfold IsUnifV at h
  rw [map_zero] at h
  exact WithZero.zero_ne_coe h

theorem unif_lt_one {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)

theorem le_one_of_unif_mul {ϖ x : w.adicCompletion E} (h : IsUnifV E w ϖ)
    (hx : Valued.v (ϖ * x) < 1) : Valued.v x ≤ 1 := by
  unfold IsUnifV at h
  rw [map_mul, h] at hx
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h0
  rw [← hm] at hx ⊢
  have h1 : Multiplicative.ofAdd (-1 : ℤ) * m < 1 := by exact_mod_cast hx
  have h2 : (-1 : ℤ) + Multiplicative.toAdd m < 0 := h1
  have h3 : m ≤ 1 := by
    show Multiplicative.toAdd m ≤ 0
    omega
  exact_mod_cast h3

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔
      Valued.v (x : w.adicCompletion E) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : w.adicCompletion E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E := by
      show Valued.v (x : w.adicCompletion E)⁻¹ ≤ 1
      rw [map_inv₀, h1, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
  · intro hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : Valued.v (x : w.adicCompletion E) * Valued.v (y : w.adicCompletion E) = 1 := by
      rw [← map_mul]
      have : (x : w.adicCompletion E) * (y : w.adicCompletion E) = 1 := congrArg Subtype.val hy
      rw [this, map_one]
    have h2 : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
    have h3 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hx
    exact absurd h1 (ne_of_lt h3)

def posR {a i : ℕ} (hi : i ≤ a) (r : Fin i) : Fin a := Fin.castLE hi r

def posS {b j : ℕ} (s : Fin (b - j)) : Fin b := ⟨j + s, by have := s.2; omega⟩

theorem corner_mem {ϖ : w.adicCompletion E} {a b i j : ℕ} (hi : i ≤ a)
    (W : latD ϖ a b i j) (p : Fin i × Fin (b - j)) :
    ϖ * W.1 (posR hi p.1) (posS p.2) ∈ w.adicCompletionIntegers E := by
  have h := W.2 (posR hi p.1) (posS p.2)
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  rw [if_pos hc] at h
  exact h

def cornerMap (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) :
    latD ϖ a b i j →+
      (Fin i × Fin (b - j) → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun W p := IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩
  map_zero' := by
    funext p
    have : (⟨_, corner_mem hi (0 : latD ϖ a b i j) p⟩ : w.adicCompletionIntegers E) = 0 :=
      Subtype.ext (by simp)
    simp only [this, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext p
    have : (⟨_, corner_mem hi (X + Y) p⟩ : w.adicCompletionIntegers E) =
        ⟨_, corner_mem hi X p⟩ + ⟨_, corner_mem hi Y p⟩ :=
      Subtype.ext (by simp [mul_add])
    simp only [this, map_add, Pi.add_apply]

theorem cornerMap_apply (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) (W : latD ϖ a b i j)
    (p : Fin i × Fin (b - j)) :
    cornerMap ϖ a b i j hi W p = IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩ := rfl

theorem ker_cornerMap {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ) (hi : i ≤ a)
    (hj : j ≤ b) :
    (cornerMap ϖ a b i j hi).ker = (intSub a b w).addSubgroupOf (latD ϖ a b i j) := by
  ext W
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro hW r s
    have hWp : ∀ p : Fin i × Fin (b - j), Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1 := by
      intro p
      have := congrFun hW p
      rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff] at this
      exact this
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · have := hWp (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩)
      have hr : posR hi ⟨(r : ℕ), hc.1⟩ = r := Fin.ext rfl
      have hs : posS (j := j) (⟨(s : ℕ) - j, by have := s.2; omega⟩ : Fin (b - j)) = s :=
        Fin.ext (by simp [posS]; omega)
      simp only [hr, hs] at this
      exact le_one_of_unif_mul h this
    · have := W.2 r s
      rw [if_neg hc] at this
      exact this
  · intro hW
    funext p
    rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
    show Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hW _ _)) (unif_lt_one h)

theorem cornerMap_surjective {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ)
    (hi : i ≤ a) (hj : j ≤ b) : Function.Surjective (cornerMap ϖ a b i j hi) := by
  intro c
  choose x hx using fun p => IsLocalRing.residue_surjective (c p)
  have h0 := unif_ne_zero h
  let M : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun r s =>
    if hc : (r : ℕ) < i ∧ j ≤ (s : ℕ) then
      ϖ⁻¹ * (x (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩) : w.adicCompletion E) else 0
  have hM : M ∈ latD ϖ a b i j := by
    intro r s
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · rw [if_pos hc]
      simp only [M, dif_pos hc]
      rw [mul_inv_cancel_left₀ h0]
      exact (x _).2
    · rw [if_neg hc]
      simp only [M, dif_neg hc]
      exact (Ov E w).zero_mem
  refine ⟨⟨M, hM⟩, ?_⟩
  funext p
  rw [cornerMap_apply, ← hx p]
  congr 1
  apply Subtype.ext
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  show ϖ * M (posR hi p.1) (posS p.2) = _
  simp only [M, dif_pos hc]
  rw [mul_inv_cancel_left₀ h0]
  congr 2
  refine Prod.ext (Fin.ext rfl) (Fin.ext ?_)
  simp [posS]

theorem relIndex_intSub_latD (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E) (h : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  have hcard : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = qV E w := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue w]
    rfl
  rw [AddSubgroup.relIndex, ← ker_cornerMap h a b i j hi hj, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (cornerMap_surjective h a b i j hi hj), AddSubgroup.card_top,
    Nat.card_fun, hcard, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end GlobalTheory.CompanionTheory.CtS.LatDiag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBoundStatement
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
theorem _root_.GlobalTheory.T.disjoint_translates_volume_bound : ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] (L : AddSubgroup G) (S : Set G), MeasurableSet S → S ⊆ L →
    ∀ (ι : Type) [Fintype ι] (f : ι → G), (∀ i, f i ∈ L) →
    (∀ i j u v, u ∈ S → v ∈ S → f i + u = f j + v → i = j) →
    (Fintype.card ι : ℝ≥0∞) * μ S ≤ μ (L : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIsoStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_degenerate_column_iso : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | exact GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | (intros; apply GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralEqSum
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.HeckeStabY

theorem exists_integral_eq_sum {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ S : Finset G, ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → (∀ g, h g = 0 → F g = 0) →
      ∫ g, F g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ s ∈ S, F s := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset G, tsupport h ⊆ ⋃ g ∈ t, (fun x => g⁻¹ * x) ⁻¹' (K : Set G) := by
    have := (show IsCompact (tsupport h) from hc).elim_nhds_subcover
      (fun g => (fun x => g⁻¹ * x) ⁻¹' (K : Set G))
      (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds
        (by simpa using K.one_mem))
    obtain ⟨t, -, ht⟩ := this
    exact ⟨t, ht⟩
  let Q : Finset (G ⧸ K) := t.image (QuotientGroup.mk : G → G ⧸ K)
  refine ⟨Q.image Quotient.out, fun F hF hz => ?_⟩
  have hinj : Set.InjOn (Quotient.out : G ⧸ K → G) (Q : Set (G ⧸ K)) :=
    fun a _ b _ e => by simpa using congrArg (QuotientGroup.mk : G → G ⧸ K) e
  rw [Finset.sum_image hinj]
  have hfib : ∀ q : G ⧸ K, {g : G | (QuotientGroup.mk g : G ⧸ K) = q} =
      (fun x => (Quotient.out q)⁻¹ * x) ⁻¹' (K : Set G) := fun q => by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]
    simp
  have hmeas : ∀ q : G ⧸ K, MeasurableSet {g : G | (QuotientGroup.mk g : G ⧸ K) = q} := fun q => by
    rw [hfib]
    exact (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hvol : ∀ q : G ⧸ K, μ {g : G | (QuotientGroup.mk g : G ⧸ K) = q} = μ (K : Set G) := fun q => by
    rw [hfib]
    exact measure_preimage_mul μ _ _
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hval : ∀ g : G, F g = F (Quotient.out (QuotientGroup.mk g : G ⧸ K)) := fun g => by
    have hm : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K := by
      rw [← QuotientGroup.eq]
      simp
    have e := hF (Quotient.out (QuotientGroup.mk g : G ⧸ K)) _ hm
    rw [mul_inv_cancel_left] at e
    exact e
  have hsum : ∀ g, F g = ∑ q ∈ Q,
      ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g := by
    intro g
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    split_ifs with hq
    · exact hval g
    · refine hz g ?_
      by_contra hne
      have hg : g ∈ tsupport h := subset_tsupport h hne
      obtain ⟨g₀, hg₀, hm⟩ := Set.mem_iUnion₂.1 (ht hg)
      refine hq (Finset.mem_image.2 ⟨g₀, hg₀, ?_⟩)
      exact QuotientGroup.eq.2 hm
  have hint : ∀ q ∈ Q, Integrable
      (({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q))) μ := fun q _ =>
    (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol]; exact hfin))
  calc ∫ g, F g ∂μ = ∫ g, ∑ q ∈ Q,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ = ∑ q ∈ Q, ∫ g,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_finset_sum Q hint
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hmeas q), Measure.real, Measure.real, hvol, Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def transOp (S : Finset (GL (Fin n) (Af E))) (c : GL (Fin n) (Af E) → ℂ) : Module.End ℂ (Sm E n) :=
  ∑ s ∈ S, c s • finRep E n s

end GlobalTheory.CompanionTheory.HeckeStabY

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuplesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfdual_measure_hermitian_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | exact GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructureStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_field_structure : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  first | exact @GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | exact GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | (intros; apply GlobalTheory.CompanionTheory.FixedPointsCM.fixedK <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumFiniteAverageBoundStatement
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
theorem _root_.GlobalTheory.T.gauss_sum_finite_average_bound : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound.twisted_integral_finite_coset_combination_bound <;> assumption)
end

