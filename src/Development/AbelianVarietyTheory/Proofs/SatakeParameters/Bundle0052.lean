import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0048
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0003
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.LocalRingCardinality.Bundle0002
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OverOnePrimeOfCardLeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem window_and_cTB_of_jumps_at_embeddings :
    ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  intro S Y h r n t _ _ hs hcard hn hg hv hth hU
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  refine ⟨fun a ha => ?_, fun e he => ?_⟩
  · have := hb a (Finset.mem_coe.1 (hsub ha))
    omega
  · unfold LocalSituation.cTBY
    rw [hg, hs, hv]
    exact cTB_le (LocalSituation.ell S) h t (n * r) e S.PD.hp _ _ hsub hc hb he hth

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMHStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_mem_box_neg_M_h : ∀ {n : ℕ} (W : WordData n), (∀ i, 0 ≤ W.sz i) → W.T1 → ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  first | exact @GlobalTheory.HTW.WordData.jumps_mem_box | exact GlobalTheory.HTW.WordData.jumps_mem_box | (intros; apply GlobalTheory.HTW.WordData.jumps_mem_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensional
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.LocalH1Finiteness

theorem matRep_apply' {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (g : ↥(GK K)) (v : Fin k → ↥LL.1) (a : Fin k) :
    matRep M g v a = ∑ b, M g a b * v b := rfl

theorem finite_continuous_cocycles_matRep (hK : Formalism.GaloisCohomology.LocalFinitenessK) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hM : Continuous fun g => M g)
    (hi : ∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) :
    Module.Finite ↥LL.1 (continuousCocycles (matRep M)) := by
  have := LL.2
  have := K.2
  let φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K) :=
    (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom
  have hφ : Continuous φ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2
  have hφs : Function.Surjective φ := (IntermediateField.fixingSubgroupEquiv K.1).symm.surjective
  have hc : ReciprocityTheory.Gal.ContAction (matRep M) := by
    refine continuous_pi fun a => ?_
    simp only [matRep_apply']
    refine continuous_finsetSum _ fun b _ =>
      Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)
    exact (hM.comp continuous_fst).matrix_elem a b
  have hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖ := fun g v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [matRep_apply']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)
  exact finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs
    (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)

theorem finite_H1fV_matRep : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1),
    Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) →
    Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  intro hK l _ P K LL k M hM hi
  have h1 := finite_continuous_cocycles_matRep hK K LL M hM hi
  have h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M)) :=
    Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 :
      finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)
  exact Module.Finite.quotient _ _

end GlobalTheory.LocalH1Finiteness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemTwistedDualJumpsWithoutBlockIff
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem half_int_eq (R : Ranks) : ((((R.t : ℤ) - 1) / 2 : ℤ) : ℚ) = ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := R.t_odd
  rw [hk]
  push_cast
  have : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [this]; push_cast; ring

theorem mem_cloud_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ cloud P j ↔ ∃ a, (X : ℚ) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold cloud
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_lows_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ lows P j ↔ ∃ a, (X : ℚ) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold lows
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_twistedDualJumpsWithoutBlock_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    u ∈ jT2 P j s ↔ (if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) ∈ cloud P j + lows P j := by
  unfold jT2 jW
  cases s
  · simp only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩
  · simp only [if_true, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩

theorem jumps_rat {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    (u ∈ jT2 P j s ↔ ((∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2) ∨ ∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2)) ∧ (u ∈ jT1 P j s ↔ u ∈ jT2 P j s ∨ ∃ c : ℕ, c < R.t ∧ -u - 1 = c) := by
  have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) =
      (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by
    split_ifs <;> push_cast <;> ring
  refine ⟨?_, ?_⟩
  · rw [mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]
  · unfold jT1 jR
    rw [Multiset.map_add, Multiset.mem_add]
    show u ∈ jT2 P j s ∨ _ ↔ _
    apply or_congr Iff.rfl
    unfold block
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple
section
open Formalism.BasicNotions Classical

namespace GlobalTheory.KFiMu0

theorem fi_eq_range' {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) (j : ℕ) : M.Fi j = Submodule.span ℂ (Set.range (M.emb j)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [← (M.emb_basis j).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    rw [← (M.emb_basis j).2, ← (M.lat j).b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem carries_one {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    {A : ColumnsAtT R C} {P : PeriodMap R C} {A' : ColumnsAtT R C'} {P' : PeriodMap R C'}
    (M : MemberForms LL embLL Pl Tau hc C A P) (M' : MemberForms LL embLL Pl Tau hc C' A' P')
    (e : ∀ j, j ≤ R.m → ((M.lat j).V ≃ₗ[LL] (M'.lat j).V)) (he : ∀ j hj x, HEq (M'.emb j (e j hj x)) (M.emb j x))
    (i : ℕ) (hi : i < R.m) (H : ∀ φ ∈ M'.Fi i, C'.K i φ ∈ M'.Fi (i + 1)) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  subst h
  have k : ∀ j, j ≤ R.m → M.Fi j = M'.Fi j := fun j hj => by
    rw [fi_eq_range', fi_eq_range']
    congr 1
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e j hj x, eq_of_heq (he j hj x)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e j hj).surjective y
      exact ⟨x, (eq_of_heq (he j hj x)).symm⟩
  intro φ hφ
  rw [k _ hi.le] at hφ
  rw [k _ hi]
  exact H φ hφ

theorem memberForms_stable_of_reference_tuple : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word), ∀ i < D.R.m,
    (∀ φ ∈ (T.fm u D.what₂.mu0).Fi i, (D.chTw u D.what₂.mu0).K i φ ∈ (T.fm u D.what₂.mu0).Fi (i + 1)) →
    ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1) :=
  fun D T u i hi H => carries_one (D.memberColumns_twistedChain_base u) (D.fm u) (T.fm u D.what₂.mu0) (T.eMu0 u) (T.eMu0_emb u) i hi H

end GlobalTheory.KFiMu0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivOfMem
section
open NumberField IsDedekindDomain GlobalTheory.Formalism.L2.Col
open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.FrobeniusOrbits
open _root_.Formalism.L2.DIV

namespace GlobalTheory.Formalism.L2.Col

namespace HostOk

variable {R : Ranks} {H : _root_.Formalism.BasicNotions.Host R} (T : Frame H)

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply (H.φ₀.comp (σ : H.E →+* H.E)) x
  have h2 := H.conjE_apply H.φ₀ (σ x)
  exact h1.trans h2.symm

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_b (g : R.Psi) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD :=
  (H.galE_mem_Psi_iff _).1 (by rw [galE_sigmaOf]; exact g.2)

theorem d_pos (H : _root_.Formalism.BasicNotions.Host R) : 0 < H.d := H.hyp.2.1.pos

theorem b_sq (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_b (H : _root_.Formalism.BasicNotions.Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem b_ne (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ≠ -H.sqrtMinusD := by
  intro h
  have h0 : H.sqrtMinusD = 0 := by
    have : (2 : H.E) * H.sqrtMinusD = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h1 := b_sq H
  rw [h0] at h1
  have h2 : (H.d : H.E) = 0 := by linear_combination h1
  have h3 : H.d = 0 := by exact_mod_cast h2
  exact (d_pos H).ne' h3

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

theorem conjK : ∃ σ₀ : (hostFields H.toHostRaw ι LL hE).K →+* ℂ, ∀ x : (hostFields H.toHostRaw ι LL hE).K,
    σ₀ (star x) = starRingEnd ℂ (σ₀ x) :=
  ⟨sig0 ι LL, fun x => (congrArg ι (CoF.val_star ι LL x)).trans (conjQb_spec ι _)⟩

end HostOk

end GlobalTheory.Formalism.L2.Col
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicitStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  first | exact @GlobalTheory.orderOf_moving_stmt | exact GlobalTheory.orderOf_moving_stmt | (intros; apply GlobalTheory.orderOf_moving_stmt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  first | exact @GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | exact GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | (intros; apply GlobalTheory.padicAlgCl_finite_dense_eq_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersLeastPowerDepthSpecStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastPowerDepth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l → LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧ ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  first | exact @GlobalTheory.depth_spec | exact GlobalTheory.depth_spec | (intros; apply GlobalTheory.depth_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersRoundedSizeBoundWindowStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roundedSizeBound_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧ (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  first | exact @GlobalTheory.HTW.bHat_window | exact GlobalTheory.HTW.bHat_window | (intros; apply GlobalTheory.HTW.bHat_window <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  first | exact @GlobalTheory.PtOfLocSplit.main | exact GlobalTheory.PtOfLocSplit.main | (intros; apply GlobalTheory.PtOfLocSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLeParametersPageHeightStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_roundedSizes_le_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  first | exact @GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | exact GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | (intros; apply GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage <;> assumption)
end

