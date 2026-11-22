import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import GroundTheory.AutomorphicForms.SmoothRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorsCommuteOnFixed
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeOpMul

open GroundTheory.Automorphic GlobalTheory.CompanionTheory.HeckeMult Zls

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_orbit_const {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.PRep.IsSmooth π)
    {K : Subgroup (GL (Fin N) k)} (hK : K ≤ KO k (Fin N)) {x y : V} (hy : ∀ g ∈ K, π g y = y)
    (hxy : ∀ l : Module.Dual ℂ V, (∀ g ∈ K, l ∘ₗ π g = l) → l x = l y)
    (f : Module.Dual ℂ V) (hf : ∀ g ∈ K, f (π g x) = f x) : f x = f y := by
  have hsm : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hmem : x - y ∈ coinvariantsKer π K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := hxy (φ ∘ₗ (coinvariantsKer π K).mkQ) (fun g hg => by
      ext u
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq _).2 (sub_mem_coinvariantsKer hg u))
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.mk_sub, map_sub, this, sub_self]
  obtain ⟨U, hU, hUz⟩ := exists_nhds_cosetSum_eq_zero hsm hmem
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun W hW => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hW
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  haveI : TotallyDisconnectedSpace (GL (Fin N) k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL (Fin N) k => g.val)
      GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  obtain ⟨M, -, -, hMU, hnorm, hfin⟩ :=
    exists_normal_subgroup (K := KO k (Fin N)) GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO hU
  haveI : (M.subgroupOf (KO k (Fin N))).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : (M.subgroupOf (KO k (Fin N))).comap (Subgroup.inclusion hK) = M.subgroupOf K := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI : (M.subgroupOf K).FiniteIndex := by
    rw [← h2]
    refine ⟨?_⟩
    rw [Subgroup.index_comap]
    exact (inferInstance : (((M.subgroupOf (KO k (Fin N))).subgroupOf
      (Subgroup.inclusion hK).range).FiniteIndex)).index_ne_zero
  haveI : Finite (K ⧸ M.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M.subgroupOf K) := Fintype.ofFinite _
  have h0 := hUz M hMU (fun g hg n hn => hnorm g (hK hg) n hn) inferInstance
  rw [map_sub, cosetSum_of_mem π (v := y) hy, sub_eq_zero, cosetSum_apply] at h0
  have h1 := congrArg f h0
  rw [map_sum, map_smul] at h1
  have h3 : ∀ q : K ⧸ M.subgroupOf K, f (π ((Quotient.out q : K) : GL (Fin N) k) x) = f x :=
    fun q => hf _ (Quotient.out q).2
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h1

abbrev idl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) : Ideal 𝒪[k] := Ideal.span {unif k ^ m}

theorem isUnit_of_sub_one_mem {m : ℕ} (hm : 1 ≤ m) (s : 𝒪[k]) (hs : s - 1 ∈ idl k m) : IsUnit s := by
  by_contra hu
  have hmax : s ∈ IsLocalRing.maximalIdeal 𝒪[k] := hu
  have hpow : unif k ^ m ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.pow_mem_of_mem _ (show unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] from irreducible_unif.not_isUnit)
      m (by omega)
  have hle : idl k m ≤ IsLocalRing.maximalIdeal 𝒪[k] := (Ideal.span_singleton_le_iff_mem _).mpr hpow
  have h1m : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.sub_mem _ hmax (hle hs)
    simpa using this
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top h1m

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin N) (Fin N) 𝒪[k])
    (hA : CongOne (idl k m) A) :
    ∃ g ∈ Km k N m, g.val = A.map (algebraMap 𝒪[k] k) := by
  have hred : A.map (Ideal.Quotient.mk (idl k m)) = 1 := by
    ext i j
    have h := (Ideal.Quotient.eq (I := idl k m)).2 (hA i j)
    rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    refine isUnit_of_sub_one_mem hm _ ?_
    refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
    have := RingHom.map_det (Ideal.Quotient.mk (idl k m)) A
    rw [this, map_one]
    have e : (Ideal.Quotient.mk (idl k m)).mapMatrix A = 1 := hred
    rw [e, Matrix.det_one]
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.mk'' A hdet),
    ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact Units.ext hred

theorem exists_cong_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ A : Matrix (Fin N) (Fin N) 𝒪[k], CongOne (idl k m) A ∧ g.val = A.map (algebraMap 𝒪[k] k) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨h.val, fun i j => ?_, rfl⟩
  have h1 : (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (idl k m)) h).val = 1 := by
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
    rw [hh]; rfl
  have h2 := congrFun (congrFun h1 i) j
  refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
  refine Eq.trans h2 ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem diagPow_val (N : ℕ) (a : Fin N → ℤ) :
    (diagPow k N a).val = Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (unif k)) ^ (a i)) := by
  ext i j
  simp [diagPow, unifU, Matrix.diagonal_apply]

theorem diagPow_add (N : ℕ) (a b : Fin N → ℤ) :
    diagPow k N (a + b) = diagPow k N a * diagPow k N b := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  apply Units.ext
  rw [Units.val_mul, diagPow_val, diagPow_val, diagPow_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [zpow_add₀ h0]

theorem exists_split {N m : ℕ} (hm : 1 ≤ m) {a b : Fin N → ℤ} (ha : Antitone a) (hb : Antitone b)
    {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ p ∈ Km k N m, ∃ l ∈ Km k N m, ∃ q ∈ Km k N m, ∃ r ∈ Km k N m,
      g = p * l ∧ diagPow k N a * p = q * diagPow k N a ∧ l * diagPow k N b = diagPow k N b * r := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  obtain ⟨A, hA, hgA⟩ := exists_cong_of_mem_Km hg
  obtain ⟨U, L, hU, hL, hUt, hLt, rfl⟩ := exists_upper_lower _ (isUnit_of_sub_one_mem hm) N A hA
  obtain ⟨Vq, hVq, hVe⟩ := conj_upper (K := k) (unif k) h0 a ha U hU hUt
  obtain ⟨Wr, hWr, hWe⟩ := conj_lower (K := k) (unif k) h0 b hb L hL hLt
  obtain ⟨p, hp, hpv⟩ := exists_mem_Km hm U hU
  obtain ⟨l, hl, hlv⟩ := exists_mem_Km hm L hL
  obtain ⟨q, hq, hqv⟩ := exists_mem_Km hm Vq hVq
  obtain ⟨r, hr, hrv⟩ := exists_mem_Km hm Wr hWr
  refine ⟨p, hp, l, hl, q, hq, r, hr, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [hgA, Units.val_mul, hpv, hlv, Matrix.map_mul]
  · rw [Units.val_mul, Units.val_mul, hpv, hqv, diagPow_val, hVe]
  · rw [Units.val_mul, Units.val_mul, hlv, hrv, diagPow_val, hWe]

theorem Km_le_KO (N m : ℕ) : Km k N m ≤ KO k (Fin N) := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem isHeckeOp_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (a b : Fin N → ℤ), Antitone a → Antitone b → ∀ (T T' : Module.End ℂ (fixed π (Zls.Km k N m))), Zls.IsHeckeOp π m (Zls.diagPow k N a) T → Zls.IsHeckeOp π m (Zls.diagPow k N b) T' → Zls.IsHeckeOp π m (Zls.diagPow k N (a + b)) (T * T') := by
  intro k _ _ _ _ N V _ _ π hπ m hm a b ha hb T T' hT hT' v l hl
  have hfix : ∀ (w : fixed π (Km k N m)), ∀ g ∈ Km k N m, π g (w : V) = w := by
    intro w g hg
    have := w.2 ⟨g, hg⟩
    simpa using this
  have hlg : ∀ g ∈ Km k N m, ∀ u, l (π g u) = l u := fun g hg u =>
    congrArg (fun t : Module.Dual ℂ V => t u) (hl g hg)
  have key := eq_of_orbit_const π hπ (Km_le_KO N m) (x := π (diagPow k N b) (v : V))
    (y := ((T' v : fixed π (Km k N m)) : V)) (hfix _)
    (fun l' hl' => hT' v l' hl') (l ∘ₗ π (diagPow k N a)) (by
      intro g hg
      obtain ⟨p, hp, l0, hl0, q, hq, r, hr, rfl, e1, e2⟩ := exists_split hm ha hb hg
      simp only [LinearMap.comp_apply]
      calc l (π (diagPow k N a) (π (p * l0) (π (diagPow k N b) (v : V))))
          = l (π (diagPow k N a * p * (l0 * diagPow k N b)) (v : V)) := by
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π q (π (diagPow k N a) (π (diagPow k N b) (π r (v : V))))) := by
            rw [e1, e2]
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π (diagPow k N a) (π (diagPow k N b) (v : V))) := by
            rw [hlg q hq, hfix v r hr])
  simp only [LinearMap.comp_apply] at key
  rw [diagPow_add, map_mul, Module.End.mul_apply, key]
  exact hT (T' v) l hl

end GlobalTheory.CompanionTheory.HeckeOpMul

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactKm
section
open Filter Topology ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.KmTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_Km_iff (N m : ℕ) (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) ∈ 𝒪[k] := by
  have ha : ((Zls.unifU k : k) ^ m) = algebraMap 𝒪[k] k (Zls.unif k ^ m) := by
    simp [Zls.unifU]
  have ha0 : ((Zls.unifU k : k) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    have h1 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      have h2 := congrArg (fun w => w.val i j) (MonoidHom.mem_ker.1 hu)
      simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h3 : (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val i j -
        (1 : Matrix (Fin N) (Fin N) k) i j = algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [hc, map_sub]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul, ← ha, mul_comm (algebraMap 𝒪[k] k c), inv_mul_cancel_left₀ ha0]
    exact c.2
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 ?_, rfl⟩
    refine Units.ext ?_
    ext i j
    have h1 := h i j
    let c : 𝒪[k] := ⟨_, h1⟩
    have h2 : algebraMap 𝒪[k] k (u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
        algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [map_mul, ← ha, map_sub]
      show _ = ((Zls.unifU k : k) ^ m)⁻¹ * _ * _
      rw [mul_comm, mul_inv_cancel_left₀ ha0]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h3 := IsFractionRing.injective 𝒪[k] k h2
    have h4 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨c, h3.symm⟩)
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
    rw [h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem continuous_entry (N m : ℕ) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have h : Continuous fun g : GL (Fin N) k => g.val i j :=
    (continuous_id.matrix_elem i j).comp Units.continuous_val
  exact continuous_const.mul (h.sub continuous_const)

theorem coe_Km_eq (N m : ℕ) : (Zls.Km k N m : Set (GL (Fin N) k)) =
    (KO k (Fin N) : Set (GL (Fin N) k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j)) ⁻¹' (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    GlobalTheory.SplitWeil.Model.isOpen_int.preimage (continuous_entry N m i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  refine GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  exact (GlobalTheory.SplitWeil.Model.isCompact_int.isClosed).preimage (continuous_entry N m i j)

end GlobalTheory.CompanionTheory.KmTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRepStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_single_segment_is_segment_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  first | exact @GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | exact GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | (intros; apply GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianCasimirRelationStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacian_casimir_relation : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.lap_sec | exact GlobalTheory.CompanionTheory.FcSmooth.lap_sec | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.lap_sec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianPowerCasimirBoundStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacian_power_casimir_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (Q : E.V →L[ℂ] E.V), LgFacts → Unimod → RCalc → ClsFacts →
    (∀ f ∈ CE E, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g)) →
    ∀ j : ℕ, ∃ C : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ ≤ C * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  first | exact @GlobalTheory.CompanionTheory.LapSec.sectionBound | exact GlobalTheory.CompanionTheory.LapSec.sectionBound | (intros; apply GlobalTheory.CompanionTheory.LapSec.sectionBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOne
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjScalar

theorem sum_card_mul_modExp {h : ℕ} (d : Fin h → ℕ) :
    ∑ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = 0 := by
  simp only [modExp, Fintype.card_fin, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : b < a
  · simp [hab, mul_comm]
  · simp [hab]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (x : ℝ) (hx : x ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := by
  have : a ≤ j := by
    have := a.2
    exact Fin.le_def.2 (by omega)
  simp [Zl.JC.zj, this]

theorem nabs_det_zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) = nabs k t ^ (d a) := by
  rw [zj_last d t j hj a]
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = t ^ (d a) := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem zj_last_scalar_modulus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h)
    (hj : j.val + 1 = h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧
      modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  constructor
  · apply Units.ext
    ext p q
    obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
    obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, zj_last d t j hj a]
      by_cases hxy : x = y
      · subst hxy
        simp [Matrix.GeneralLinearGroup.scalar]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
        simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
    · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
        hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
      rw [leviEmb_apply_ne k _ _ hab]
      simp [Matrix.GeneralLinearGroup.scalar, this]
  · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
    simp only [modulus, nabs_det_zj_last d t j hj]
    have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
        nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
      rw [zpow_mul, zpow_natCast]
    simp only [this]
    rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]

end GlobalTheory.CompanionTheory.ZjScalar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLevi
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.LeviBlockIdx

theorem leviEmb_mem_levi_blockIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y

end GlobalTheory.CompanionTheory.LeviBlockIdx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

variable (E r s) in

def blockOne (x : Lie E r) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks (Matrix.of x) 0 0 1))

theorem contDiff_blockOne : ContDiff ℝ (⊤ : ℕ∞) (blockOne E r s) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · exact contDiff_apply_apply ℝ (Cinf E) i' j'
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem blockOne_val (y : GL (Fin r) (Cinf E)) :
    blockOne E r s (toL (y : Matrix (Fin r) (Fin r) (Cinf E))) =
      toL ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := by
  rw [GlobalTheory.SmGL.val_emb₂]
  rfl

theorem exists_val_of_mem_invSet {x : Lie E r} (hx : x ∈ invSet E r) :
    ∃ y : GL (Fin r) (Cinf E), x = toL (y : Matrix (Fin r) (Fin r) (Cinf E)) :=
  ⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩

theorem toL_val_mem_invSet (y : GL (Fin r) (Cinf E)) :
    toL (y : Matrix (Fin r) (Fin r) (Cinf E)) ∈ invSet E r :=
  show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit

theorem sm_lev_slice (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ)
    (hF : F ∈ Sm E (r + s)) : (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  intro g
  have hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
    rw [blockOne_val]
    exact toL_val_mem_invSet _
  have hcomp := (hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps
  refine hcomp.congr fun x hx => ?_
  obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
  rw [Function.comp_apply, blockOne_val, chart_val, chart_val]
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [← e1, lev_mul_one]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.GKLocalProof

theorem invT_eq_invTranspose {A : Type} [CommRing A] (N : ℕ) :
    (invT : GL (Fin N) A →* GL (Fin N) A) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N A :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem gkLocal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  intro k _ _ _ _ hA N V _ _ π hs hi
  rw [invT_eq_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi

end GlobalTheory.CompanionTheory.GKLocalProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbertStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  first | exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll | exact GlobalTheory.CompanionTheory.HilbMoll.stepMoll | (intros; apply GlobalTheory.CompanionTheory.HilbMoll.stepMoll <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegreesStatement
section
open GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_of_strings_determines_points_degrees : ∀ {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ), (∀ i, 1 ≤ d i) → (∀ j, 1 ≤ d' j) → GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d' → ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  first | exact @GlobalTheory.CompanionTheory.Rigid.strings_rigid | exact GlobalTheory.CompanionTheory.Rigid.strings_rigid | (intros; apply GlobalTheory.CompanionTheory.Rigid.strings_rigid <;> assumption)
end

