import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.SDBound

variable {D : D7}

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_mul_isIntegral_fin {n : ℕ} (z : Fin n → Fin n → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l k, IsIntegral ℤ ((d : D.host.E) * z l k) := by
  classical
  choose c hc hi using fun p : Fin n × Fin n => exists_nat_mul_isIntegral (z p.1 p.2)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l k => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ (l, k)), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (l, k))
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem finPart_incA_mem {o : D.host.E} (ho : IsIntegral ℤ o) : finPart D (incA D o) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩

theorem hermAt_single (S : HSp D) (y : Fin S.rank → AE D) (k : Fin S.rank) (a : AE D) :
    hermAt S y (Pi.single k a) = cA D a * (gA S *ᵥ y) k := by
  unfold hermAt
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, RingHom.map_zero]
    simp only [zero_mul, Finset.sum_const_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem exists_mul_mem_intAt : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v) := by
  intro D S v Λ ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  obtain ⟨d, hd, hint⟩ := exists_nat_mul_isIntegral_fin (fun l k => (S.gram)⁻¹ l k)
  refine ⟨d * m, Nat.mul_pos hd hm, fun y hy l => ⟨Ideal.mul_mem_left _ _ (hsupp y hy l), ?_⟩⟩
  have key : ∀ k, finPart D ((m : AE D) * (gA S *ᵥ y) k) ∈ intAE D := fun k => by
    have hx : (m : AE D) • (Pi.single k ε : Fin S.rank → AE D) ∈ Λ := by
      refine hmul _ fun i => ?_
      by_cases hi : i = k
      · rw [hi, Pi.single_eq_same]; exact hε
      · rw [Pi.single_eq_of_ne hi]; exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    have h1 := (((hdual y (hsupp y hy)).1 hy) _ hx).2
    rwa [← Pi.single_smul', smul_eq_mul, hermAt_single, RingHom.map_mul (cA D), map_natCast, hc, mul_assoc,
      hact _ (mulVec_mem_idAt _ (hsupp y hy) k)] at h1
  have e1 : y l = ∑ k, incA D ((S.gram)⁻¹ l k) * (gA S *ᵥ y) k := by
    have : giA S *ᵥ (gA S *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, giA_mul_gA, Matrix.one_mulVec]
    exact (congrFun this l).symm
  have e2 : ((d * m : ℕ) : AE D) * y l =
      ∑ k, incA D ((d : D.host.E) * (S.gram)⁻¹ l k) * ((m : AE D) * (gA S *ᵥ y) k) := by
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e2, map_sum]
  refine sum_mem fun k _ => ?_
  rw [RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (finPart_incA_mem (hint l k)) (key k)

end GlobalTheory.IwaPlace.SDBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (c : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * c ∈ 𝒪[k] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[k]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : b ∣ ((Nat.card 𝓀[k] ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[k] ^ m, pow_pos Nat.card_pos m, ?_⟩
  have hb' : (algebraMap 𝒪[k] k b) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
  have : ((Nat.card 𝓀[k] ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) =
      algebraMap 𝒪[k] k (d * a) := by
    rw [← map_natCast (algebraMap 𝒪[k] k), hd, map_mul, map_mul]
    field_simp
  rw [this]
  exact (d * a).2

theorem exists_nat_mul_mem_fin {ι : Type} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  choose N hN h using fun i => exists_nat_mul_mem (c i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_mem {n n' m m' : Type} [Fintype n] [Fintype n'] {N : ℕ} (b : Matrix m n k) (b' : Matrix n' m' k)
    (hb : ∀ i a, (N : k) * b i a ∈ 𝒪[k]) (hb' : ∀ a j, (N : k) * b' a j ∈ 𝒪[k]) (x : Matrix n n' k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) (i : m) (j : m') : ((N * N : ℕ) : k) * (b * x * b') i j ∈ 𝒪[k] := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine sum_mem fun a _ => sum_mem fun c _ => ?_
  have : ((N * N : ℕ) : k) * (b i c * x c a * b' a j) = ((N : k) * b i c) * x c a * ((N : k) * b' a j) := by
    push_cast; ring
  rw [this]
  exact mul_mem (mul_mem (hb i c) (hx c a)) (hb' a j)

end GlobalTheory.FinPl.RdInt

theorem GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × n => β.b x.1 x.2) (fun x : n' × Fin S.rank => α.b' x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  refine ⟨K * (N₀ * N₀), Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀), fun t ht hrd => ?_⟩
  have hent := GlobalTheory.FinPl.RdInt.entry_mem β.b α.b' (fun i a => h₀ (Sum.inl (i, a))) (fun a j => h₀ (Sum.inr (a, j)))
    (rd α β t) hrd
  have htw := GlobalTheory.FinPl.HalfInd.wr_rd α β ht
  have hu : IsHalf p.e ((N₀ * N₀) • t) := (GlobalTheory.PlaceModel.isHalf_iff S T).2
    ((GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) _)
  have hui : ∀ i j, toEAf D (((N₀ * N₀) • t) i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have h1 : ((N₀ * N₀) • t) i j = p.sec (((N₀ * N₀ : ℕ) : k) * (β.b * rd α β t * α.b') i j) := by
      rw [← nsmul_eq_mul, map_nsmul, ← GlobalTheory.FinPl.HalfInd.wr_apply, htw]
      rfl
    rw [h1]
    exact GlobalTheory.PlaceCoord.toEAf_mem ((p.int_iff _).1 (hent i j))
  have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) hu) hui
  have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h1).1
  have hh : K • (N₀ * N₀) • t ∈ GlobalTheory.PlaceModel.half S T p.e :=
    (GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) _
  rw [(GlobalTheory.PlaceModel.mem_half S T).1 hh] at h2
  rwa [mul_nsmul']

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPartitionOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatPartition

theorem finite_ratW_mem {D : D7} (A T : HSp D) {C : Set (WO A T)} (hC : IsCompact C) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ C}.Finite := by
  obtain ⟨i1, -, -, i4, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i4; haveI := i5
  have hLc : IsClosed (ratMx D T.rank A.rank : Set (Mx D T.rank A.rank)) := AddSubgroup.isClosed_of_discrete
  let φ : Matrix (Fin T.rank) (Fin A.rank) D.host.E → ratMx D T.rank A.rank := fun γ => ⟨ratW T A γ, γ, rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h)
  have hs : IsCompact ((↑) ⁻¹' C : Set (ratMx D T.rank A.rank)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hC.inter_right hLc
  exact (hs.finite_of_discrete.preimage (f := φ) hφ.injOn : _)

theorem exists_partition_one : ∀ (D : D7) (A T : HSp D), ∃ χ : WO A T → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
    (∀ u, 0 ≤ χ u) ∧ ∀ u, HasSum (fun γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E => χ (ratW T A γ + u)) 1 := by
  intro D A T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i2; haveI := i4
  haveI : RegularSpace (Mx D T.rank A.rank) := IsTopologicalAddGroup.regularSpace _
  haveI : ContinuousSub (Mx D T.rank A.rank) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hS : IsCompact (tsupport f) := hfc
  let g : Matrix (Fin T.rank) (Fin A.rank) D.host.E → WO A T → ℝ := fun γ u => f (ratW T A γ + u)
  have hgc : ∀ γ, Continuous (g γ) := fun γ => f.continuous.comp (continuous_add_left (ratW T A γ : WO A T))
  have hfin : ∀ N : Set (WO A T), IsCompact N → {γ | (Function.support (g γ) ∩ N).Nonempty}.Finite := by
    intro N hN
    refine (finite_ratW_mem A T ((hS.prod hN).image (continuous_fst.sub continuous_snd))).subset ?_
    rintro γ ⟨u, hu, huN⟩
    exact ⟨(ratW T A γ + u, u), ⟨subset_tsupport _ hu, huN⟩, add_sub_cancel_right _ _⟩
  have hlf : LocallyFinite fun γ => Function.support (g γ) := by
    intro u
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds u
    exact ⟨N, hN, hfin N hNc⟩
  have hpt : ∀ u, (Function.support fun γ => g γ u).Finite := by
    intro u
    refine (hfin {u} isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨u, hγ, rfl⟩
  let s : WO A T → ℝ := fun u => ∑ᶠ γ, g γ u
  have hs_cont : Continuous s := continuous_finsum hgc hlf
  have hg0 : ∀ γ u, 0 ≤ g γ u := fun γ u => (hf01 _).1
  have hs1 : ∀ u, 1 ≤ s u := by
    intro u
    obtain ⟨x, ⟨γ, rfl⟩, hx⟩ := hKc u
    have h1 : g γ u = 1 := hf1 hx
    rw [← h1]
    exact single_le_finsum γ (hpt u) (fun j => hg0 j u)
  have hs_inv : ∀ γ₀ u, s (ratW T A γ₀ + u) = s u := by
    intro γ₀ u
    have e : ∀ γ, g γ (ratW T A γ₀ + u) = g (γ + γ₀) u := by
      intro γ
      simp only [g, ratW]
      rw [Matrix.map_add _ (map_add (incA D)) γ γ₀, add_assoc]
    simp only [s, e]
    exact finsum_comp_equiv (Equiv.addRight γ₀) (f := fun γ => g γ u)
  have hpos : ∀ u, 0 < s u := fun u => zero_lt_one.trans_le (hs1 u)
  refine ⟨fun u => f u * (s u)⁻¹, f.continuous.mul (hs_cont.inv₀ fun u => (hpos u).ne'), hfc.mul_right,
    fun u => mul_nonneg (hf01 u).1 (inv_nonneg.2 (hpos u).le), fun u => ?_⟩
  have e : (fun γ => f (ratW T A γ + u) * (s (ratW T A γ + u))⁻¹) = fun γ => g γ u * (s u)⁻¹ := by
    funext γ
    rw [hs_inv]
  simp only [e]
  have h : HasSum (fun γ => g γ u) (∑ γ ∈ (hpt u).toFinset, g γ u) :=
    hasSum_sum_of_ne_finset_zero (fun γ hγ => by simpa using hγ)
  rw [← finsum_eq_sum _ (hpt u)] at h
  have h2 := h.mul_right (s u)⁻¹
  rwa [mul_inv_cancel₀ (hpos u).ne'] at h2

end GlobalTheory.RatPartition

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem exists_integral_multiplier {k : Type} [Field k] [ValuativeRel k] (a : k) :
    ∃ b : k, b ≠ 0 ∧ b ∈ 𝒪[k] ∧ b * a ∈ 𝒪[k] := by
  by_cases ha : a ∈ 𝒪[k]
  · exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by rintro rfl; exact ha (Subring.zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero ha0, ?_, by simp [ha0, Subring.one_mem]⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    push_neg at ha
    exact inv_le_one_of_one_le₀ ha.le

theorem exists_common_integral_multiplier {k : Type} [Field k] [ValuativeRel k]
    {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ c : k, c ≠ 0 ∧ c ∈ 𝒪[k] ∧ ∀ i, c * f i ∈ 𝒪[k] := by
  classical
  choose b hb0 hbO hbf using fun i => exists_integral_multiplier (f i)
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i,
    Subring.prod_mem _ fun i _ => hbO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i), mul_comm (b i), mul_assoc]
  exact Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hbO j) (hbf i)

theorem enl_scalar_denominator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk
  obtain ⟨c, hc0, hcO, hc⟩ := exists_common_integral_multiplier
    (fun p : Y × Y × Y' × Y' => (↑(hk⁻¹) : Matrix Y Y k) p.1 p.2.1 * (↑gk : Matrix Y' Y' k) p.2.2.1 p.2.2.2)
  refine ⟨Units.mk0 c hc0, fun zk hz => ⟨?_, ?_⟩⟩
  · intro x hx r q
    have : ((↑((hk * zk⁻¹)⁻¹) : Matrix Y Y k)) = c • (↑(hk⁻¹) : Matrix Y Y k) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hz]
      simp
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    have h1 := hc (r, s, t, q)
    have h2 := hx s t
    simp only at h1
    have : c * ((↑(hk⁻¹) : Matrix Y Y k) r s * x s t * (↑gk : Matrix Y' Y' k) t q) =
      (c * ((↑(hk⁻¹) : Matrix Y Y k) r s * (↑gk : Matrix Y' Y' k) t q)) * x s t := by ring
    rw [this]
    exact Subring.mul_mem _ h1 h2
  · intro x hx r q
    rw [inv_inv, hz]
    simp only [Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul, Units.val_mk0]
    exact Subring.mul_mem _ hcO (hx r q)

end GlobalTheory.LocOm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SmallLevel

theorem exists_open_subgroup (F : Type) [Field F] [NumberField F] (V : Set (Af F)) (hV : V ∈ 𝓝 (0 : Af F)) :
    ∃ S : AddSubgroup (Af F), IsOpen (S : Set (Af F)) ∧ (S : Set (Af F)) ⊆ V := by
  obtain ⟨M, hM, hMV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F V hV
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  refine ⟨S, S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hMV a ha

theorem infPart_smul_eq_zero {D : D7} (y : Af D.host.F) (x : AE D) : infPart D (pairA D.host.F 0 y • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 y)) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_closed_level (D : D7) (m n : ℕ) (N : Set (Mx D m n)) (hN : N ∈ 𝓝 (0 : Mx D m n)) :
    ∃ K : AddSubgroup (Mx D m n), IsClosed (K : Set (Mx D m n)) ∧ (K : Set (Mx D m n)) ⊆ N ∧
      (∀ u ∈ K, u.map (infPart D) = 0) ∧
      ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AE D) := IsModuleTopology.topologicalAddGroup (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (InfiniteAdeleRing D.host.F) := inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) → Mx D m n :=
    fun x i j => ∑ k, pairA D.host.F 0 (x (i, j, k)) • B k
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
        pairA D.host.F 0 (x (i, j, k)) := continuous_const.prodMk (continuous_apply _)
    exact h1.smul continuous_const
  have h0 : Φ 0 = 0 := by
    funext i j
    refine Finset.sum_eq_zero fun k _ => ?_
    exact zero_smul (AF D.host.F) (B k)
  have h1 : Φ ⁻¹' N ∈ 𝓝 0 := hΦ.continuousAt.preimage_mem_nhds (h0 ▸ hN)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  obtain ⟨S, hS, hSt⟩ := exists_open_subgroup D.host.F (⋂ p, t p) (Filter.iInter_mem.mpr ht)
  let c : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Mx D m n →+ AF D.host.F := fun p =>
    { toFun := fun u => B.coord p.2.2 (u p.1 p.2.1)
      map_zero' := map_zero _
      map_add' := fun u u' => map_add _ _ _ }
  have hc : ∀ p, Continuous (c p) := fun p =>
    (IsModuleTopology.continuous_of_linearMap (B.coord p.2.2)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  let U : AddSubgroup (Mx D m n) := ⨅ p, S.comap ((sndA D.host.F).toRingHom.toAddMonoidHom.comp (c p))
  let Z : AddSubgroup (Mx D m n) := ⨅ p, ((fstA D.host.F).toRingHom.toAddMonoidHom.comp (c p)).ker
  have hU : ∀ u, u ∈ U ↔ ∀ p, (c p u).2 ∈ S := fun u => AddSubgroup.mem_iInf
  have hZ : ∀ u, u ∈ Z ↔ ∀ p, (c p u).1 = 0 := fun u => AddSubgroup.mem_iInf
  have hUe : (U : Set (Mx D m n)) = ⋂ p, (fun u => (c p u).2) ⁻¹' S := by
    ext u; rw [Set.mem_iInter]; exact hU u
  have hZe : (Z : Set (Mx D m n)) = ⋂ p, {u | (c p u).1 = 0} := by
    ext u; rw [Set.mem_iInter]; exact hZ u
  have hrec : ∀ u ∈ Z, Φ (fun p => (c p u).2) = u := by
    intro u hu
    funext i j
    conv_rhs => rw [← B.sum_repr (u i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Prod.ext ((hZ u).mp hu (i, j, k)).symm rfl
  refine ⟨U ⊓ Z, ?_, ?_, ?_, U, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf, hUe, hZe]
    exact (isClosed_iInter fun p => (S.isClosed_of_isOpen hS).preimage (continuous_snd.comp (hc p))).inter
      (isClosed_iInter fun p => isClosed_eq (continuous_fst.comp (hc p)) continuous_const)
  · intro u hu
    have h4 : (fun p => (c p u).2) ∈ I.pi t := fun p _ => Set.mem_iInter.mp (hSt ((hU u).mp hu.1 p)) p
    have h5 := hsub h4
    rwa [Set.mem_preimage, hrec u hu.2] at h5
  · intro u hu
    funext i j
    have h4 : ∑ k, pairA D.host.F 0 (c (i, j, k) u).2 • B k = u i j := congrFun (congrFun (hrec u hu.2) i) j
    rw [Matrix.map_apply, ← h4]
    exact (infPart D).toAddMonoidHom.ker.sum_mem fun k _ => infPart_smul_eq_zero _ _
  · rw [hUe]
    exact isOpen_iInter_of_finite fun p => hS.preimage (continuous_snd.comp (hc p))
  · intro u hu hu'
    refine ⟨hu, (hZ u).mpr fun p => ?_⟩
    have h2 := GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu' p.1) p.2.1)
    have h3 : GlobalTheory.FinTranslate.eInf D * c p u = 0 := by
      have := congrArg (B.coord p.2.2) h2
      rwa [map_smul, map_zero, smul_eq_mul] at this
    exact (one_mul _).symm.trans (congrArg Prod.fst h3)

theorem exists_small_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  intro D ψ hψ A T N hN
  haveI : LocallyCompactSpace (WO A T) := (GlobalTheory.MixModel.lattice_Mx D T.rank A.rank).2.1
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : WO A T)
  have hs : Continuous fun p : WO A T × WO A T => (symplOH A T p.1 p.2).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)
  have h2 := hs.continuousAt.preimage_mem_nhds (x := (0, 0)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by
      have h0 : (symplOH A T (0 : WO A T) 0).2 = 0 := congrArg Prod.snd (GlobalTheory.FinTranslate.symplOH_zero_left A T 0)
      have h1 := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
      rwa [← h0] at h1)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp h2
  obtain ⟨K, hK, hKN, hKf, hKU⟩ := exists_closed_level D T.rank A.rank (N ∩ C ∩ (P ∩ Q))
    (Filter.inter_mem (Filter.inter_mem hN hC0) (Filter.inter_mem hP hQ))
  refine ⟨K, hC.of_isClosed_subset hK fun u hu => (hKN hu).1.2, fun u hu => (hKN hu).1.1, hKf, hKU,
    fun u hu u' hu' => ?_⟩
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH A T u u' = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin (hKf u' hu'),
      GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH A T u u' = pairA D.host.F 0 (symplOH A T u u').2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  rw [h4]
  have h5 := hPQ (Set.mk_mem_prod (hKN hu).2.1 (hKN hu').2.2)
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h5
  exact h5

end GlobalTheory.SmallLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryEmbeddingPreimageOfFixesAnisotropicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ k : GA D S, mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ) → ∃ h : GA D A, k = o.emb (h, 1) := by
  first | exact @GlobalTheory.exists_emb_of_fixes_lineVec | exact GlobalTheory.exists_emb_of_fixes_lineVec | (intros; apply GlobalTheory.exists_emb_of_fixes_lineVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosetsStatement
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_dualIndicator_add_nonzeroCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) = fpair χ e μ (vecInd L) (dualInd L) := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets <;> assumption)
end

