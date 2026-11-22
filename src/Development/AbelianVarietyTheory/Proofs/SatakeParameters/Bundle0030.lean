import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosetsStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_heckeSet_split_place_cosets : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)), (∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → κ ∈ J) → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (NumberField.maximalRealSubfield L)) (k : ℕ), Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFinCong.finite_image_tSet_cong | exact GlobalTheory.TSetFinCong.finite_image_tSet_cong | (intros; apply GlobalTheory.TSetFinCong.finite_image_tSet_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChangeStatement
section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧ ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b → ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  first | (exact @GlobalTheory.W1.Base.forms_baseChange) | (exact GlobalTheory.W1.Base.forms_baseChange) | (intros; apply GlobalTheory.W1.Base.forms_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuotStatement
section
open GlobalTheory.PD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  first | (exact @GlobalTheory.PD.isArtinianRing_fib_quot) | (exact GlobalTheory.PD.isArtinianRing_fib_quot) | (intros; apply GlobalTheory.PD.isArtinianRing_fib_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLe
section
noncomputable section

open GlobalTheory.LatHecke

namespace GlobalTheory.SubIdxCount

noncomputable def hc (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))

theorem hc_zero_right (q r : ℕ) : hc q r 0 = 1 := by
  induction r with
  | zero => simp [hc]
  | succ r ih => simp [hc, ih]

theorem hc_le (q : ℕ) (hq : 1 ≤ q) (r n : ℕ) : hc q r n ≤ (n + 1) ^ r * (q ^ (r - 1)) ^ n := by
  induction r generalizing n with
  | zero => simp only [hc]; split_ifs <;> simp
  | succ r ih =>
    simp only [hc]
    calc ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1), (n + 1) ^ r * q ^ (r * n) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          calc hc q r k * q ^ (r * (n - k))
              ≤ ((k + 1) ^ r * (q ^ (r - 1)) ^ k) * q ^ (r * (n - k)) :=
                Nat.mul_le_mul_right _ (ih k)
            _ = (k + 1) ^ r * q ^ ((r - 1) * k + r * (n - k)) := by
                rw [← pow_mul, pow_add]; ring
            _ ≤ (n + 1) ^ r * q ^ (r * n) := by
                apply Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                apply Nat.pow_le_pow_right hq
                have h1 : (r - 1) * k ≤ r * k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                have h2 : r * k + r * (n - k) = r * n := by
                  rw [← Nat.mul_add, Nat.add_sub_cancel' hk']
                omega
      _ = (n + 1) ^ (r + 1) * (q ^ (r + 1 - 1)) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_sub_cancel, ← pow_mul,
            pow_succ]
          ring

theorem one_sub_mul_geom (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.mk (fun n => c ^ n) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
      pow_succ]
    ring

def polP (q r : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range r, (1 - Polynomial.C ((q : ℂ) ^ i) * Polynomial.X)

theorem polP_mul_hc (q r : ℕ) :
    (polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ)) = 1 := by
  induction r with
  | zero =>
    ext n; simp [polP, hc, PowerSeries.coeff_one]
  | succ r ih =>
    have hmk : PowerSeries.mk (fun n => (hc q (r + 1) n : ℂ)) =
        PowerSeries.mk (fun n => (hc q r n : ℂ)) * PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n) := by
      ext n
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          PowerSeries.coeff j (PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)))]
      simp [hc, pow_mul]
    rw [polP, Finset.prod_range_succ, Polynomial.coe_mul, ← polP, hmk]
    calc (polP q r : PowerSeries ℂ) * ((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X :
          Polynomial ℂ) : PowerSeries ℂ) * (PowerSeries.mk (fun n => (hc q r n : ℂ)) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n))
        = ((polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          (((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)) := by ring
      _ = 1 := by
        rw [ih, one_mul]
        rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
          Polynomial.coe_X]
        exact one_sub_mul_geom ((q : ℂ) ^ r)

theorem coeff_relation (q r n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (polP q r).coeff k * (hc q r (n - k) : ℂ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) (polP_mul_hc q r)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (polP q r : PowerSeries ℂ) *
      PowerSeries.coeff j (PowerSeries.mk (fun n => (hc q r n : ℂ))))] at h
  simpa [PowerSeries.coeff_one, show n ≠ 0 by omega, Polynomial.coeff_coe] using h

end GlobalTheory.SubIdxCount

namespace GlobalTheory.SubIdxCount

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

theorem elem_coeff (r : ℕ) (L : Lat O K r) (k : ℕ) :
    (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) =
      (polP (qRes O) r).coeff k := by
  obtain ⟨-, -, hemp, hX⟩ := GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial O K r L
  have hQP : (∑ j ∈ Finset.range (r + 1), Polynomial.C ((-1 : ℂ) ^ j *
      (qRes O : ℂ) ^ (j * (j - 1) / 2) * ((subElem j L).ncard : ℂ)) * Polynomial.X ^ j) =
      polP (qRes O) r := by
    apply Polynomial.funext
    intro x
    rw [polP, Polynomial.eval_finsetSum, Polynomial.eval_prod]
    simpa using hX x
  rw [← hQP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have : r < k := by simp at hk; omega
    rw [hemp k this]; simp

theorem ncard_subIdx_eq (r : ℕ) : ∀ (n : ℕ) (L : Lat O K r),
    (subIdx n L).ncard = hc (qRes O) r n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [subIdx_zero, Set.ncard_singleton, hc_zero_right]
  have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r ℂ (fun _ => (1 : ℂ)) n L hn
  have hall : ∀ (m : ℕ) (M : Lat O K r),
      heckeAll m (fun _ => (1 : ℂ)) M = ((subIdx m M).ncard : ℂ) := by
    intro m M
    rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite m M)]
    simp
  have hterm : ∀ k ∈ Finset.range n,
      ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
        heckeElem (k + 1) (heckeAll (n - (k + 1)) (fun _ => (1 : ℂ))) L =
      (polP (qRes O) r).coeff (k + 1) * (hc (qRes O) r (n - (k + 1)) : ℂ) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hc' : heckeAll (n - (k + 1)) (fun (_ : Lat O K r) => (1 : ℂ)) =
        fun (_ : Lat O K r) => (hc (qRes O) r (n - (k + 1)) : ℂ) := by
      funext M; rw [hall, ih _ (by omega) M]
    rw [hc', heckeElem_eq_sum, Finset.sum_const, ← Set.ncard_eq_toFinset_card _
      (subElem_finite _ L), ← elem_coeff r L (k + 1), smul_eq_mul, nsmul_eq_mul]
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_range_succ'] at hid
  rw [hsum] at hid
  have hrel := coeff_relation (qRes O) r n hn
  rw [Finset.sum_range_succ'] at hrel
  have h0 := elem_coeff r L 0
  rw [subElem_zero, Set.ncard_singleton] at h0
  rw [heckeElem_zero, hall] at hid
  simp only [pow_zero, zero_mul, Nat.zero_div, Nat.cast_one, mul_one, Nat.sub_zero,
    one_smul] at hid h0
  rw [← h0, one_mul] at hrel
  have : ((subIdx n L).ncard : ℂ) = (hc (qRes O) r n : ℂ) := by
    linear_combination hid - hrel
  exact_mod_cast this

theorem ncard_subIdx_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (n : ℕ) (L : Lat O K r),
    ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  intro O K _ _ _ _ _ _ _ r n L
  rw [ncard_subIdx_eq r n L]
  have h := hc_le (qRes O) (one_lt_qRes (O := O)).le r n
  exact_mod_cast h

end GlobalTheory.SubIdxCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
section
open Formalism.MainNotions.N

namespace GlobalTheory

open scoped BigOperators

theorem ssRep_of_normal_finiteIndex : ∀ (H k : Type) [Group H] [Field k] [CharZero k] (a : ℕ)
    (ρ : H →* GL (Fin a) k) (N : Subgroup H), N.Normal → N.FiniteIndex →
    IsSSRep (ρ.comp N.subtype) → IsSSRep ρ := by
  intro H k _ _ _ a ρ N hN hfi hss W hW
  classical

  let T : H → (Fin a → k) →ₗ[k] (Fin a → k) := fun g => Matrix.mulVecLin (ρ g : Matrix (Fin a) (Fin a) k)
  have hTapp : ∀ g v, T g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := fun g v => rfl
  have hTmul : ∀ g h v, T (g * h) v = T g (T h v) := by
    intro g h v
    simp only [hTapp, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hTone : ∀ v, T 1 v = v := by
    intro v; simp [hTapp]
  have hTinv : ∀ g v, T g (T g⁻¹ v) = v := by
    intro g v; rw [← hTmul, mul_inv_cancel, hTone]
  have hTinv' : ∀ g v, T g⁻¹ (T g v) = v := by
    intro g v; rw [← hTmul, inv_mul_cancel, hTone]
  have hWN : IsInv (ρ.comp N.subtype) W := fun n v hv => hW n v hv
  obtain ⟨W', hW', hc⟩ := hss W hWN
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ Submodule.projectionOnto W W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (Submodule.projectionOnto W W' hc v).2
  have hpid : ∀ w ∈ W, p w = w := by
    intro w hw
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hc ⟨w, hw⟩)
  have hp0 : ∀ w ∈ W', p w = 0 := by
    intro w hw
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_right hc ⟨w, hw⟩)
  have hpN : ∀ n ∈ N, ∀ v, T n (p v) = p (T n v) := by
    intro n hn v
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : T n w ∈ W := hW n w hw
    have h2 : T n w' ∈ W' := hW' ⟨n, hn⟩ w' hw'
    rw [map_add p w w', hpid w hw, hp0 w' hw', add_zero, map_add (T n), map_add p, hpid _ h1,
      hp0 _ h2, add_zero]
  let C : H → (Fin a → k) →ₗ[k] (Fin a → k) := fun g => T g ∘ₗ p ∘ₗ T g⁻¹
  have hC : ∀ g n, n ∈ N → C (g * n) = C g := by
    intro g n hn
    refine LinearMap.ext fun v => ?_
    simp only [C, LinearMap.comp_apply, mul_inv_rev]
    rw [hTmul, hTmul, hpN n hn, hTinv]
  let C' : H ⧸ N → (Fin a → k) →ₗ[k] (Fin a → k) :=
    Quotient.lift C (by
      intro g g' hgg'
      have hm : g⁻¹ * g' ∈ N := QuotientGroup.leftRel_apply.mp hgg'
      have : g' = g * (g⁻¹ * g') := by group
      rw [this, hC g _ hm])
  have hC'mk : ∀ g : H, C' (g : H ⧸ N) = C g := fun g => rfl
  haveI : Fintype (H ⧸ N) := Fintype.ofFinite _
  have hm0 : (Fintype.card (H ⧸ N) : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let q : (Fin a → k) →ₗ[k] (Fin a → k) := (Fintype.card (H ⧸ N) : k)⁻¹ • ∑ c : H ⧸ N, C' c
  have hqW : ∀ v, q v ∈ W := by
    intro v
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply]
    refine W.smul_mem _ (W.sum_mem fun c _ => ?_)
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [hC'mk]
      exact hW g _ (hpW _)
  have hqid : ∀ w ∈ W, q w = w := by
    intro w hw
    have hterm : ∀ c : H ⧸ N, C' c w = w := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H g =>
        rw [hC'mk]
        simp only [C, LinearMap.comp_apply]
        have hm : T g⁻¹ w ∈ W := hW g⁻¹ w hw
        rw [hpid _ hm, hTinv]
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply, hterm,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hm0, one_smul]
  have hcomm : ∀ h : H, ∀ c : H ⧸ N, ∀ v, T h (C' c v) = C' (h • c) (T h v) := by
    intro h c v
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, hC'mk, hC'mk]
      simp only [C, LinearMap.comp_apply, smul_eq_mul, mul_inv_rev]
      rw [hTmul, hTmul, hTinv']
  have hqT : ∀ h v, T h (q v) = q (T h v) := by
    intro h v
    simp only [q, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
      hcomm]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (H ⧸ N)) (fun c => C' c (T h v))
  refine ⟨LinearMap.ker q, ?_, ?_⟩
  · intro h v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hTapp, ← hqT, hv, map_zero]
  · have hf : ∀ x : W, (q.codRestrict W hqW) x = x := by
      intro x; ext1; exact hqid x x.2
    have := LinearMap.isCompl_of_proj hf
    rwa [LinearMap.ker_codRestrict] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitSieve_mem_of_fibrePointsLE : ∀ (n : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    FibrePointsLE f n → splitSieve f (𝟙 X) ∈ Scheme.etaleTopology X := by
  intro n
  induction n with
  | zero =>
    intro Z X f _ _ h
    have : IsEmpty Z := GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h
    have hs : Splits f (𝟙 X ≫ 𝟙 X) := GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))
    have hmem : splitSieve f (𝟙 X) (𝟙 X) := ⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩
    rw [Sieve.id_mem_iff_eq_top] at hmem
    rw [hmem]; exact (Scheme.etaleTopology).top_mem X
  | succ n ih =>
    intro Z X f _ _ h
    obtain ⟨hfin, het⟩ := GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f
    have hg := ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)
    refine GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)
    · refine (Scheme.etaleTopology).superset_covering ?_ hg
      rintro V u ⟨W, w, v, hv, rfl⟩
      have h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z) := GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv
      have h2 : Splits f ((v ≫ 𝟙 Z) ≫ f) := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1
      exact ⟨W, w, v ≫ f, by simpa using h2, by simp⟩
    · exact ⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩

theorem splitSieve_mem : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X),
    splitSieve f x ∈ Scheme.etaleTopology S := by
  intro Z X S f _ _ x
  let 𝒰 := S.affineCover
  have hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S :=
    Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)
  refine (Scheme.etaleTopology).transitive hU _ ?_
  rintro Y u ⟨W, w, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable w ?_
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))
  have hi := splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn
  refine (Scheme.etaleTopology).superset_covering ?_ hi
  rintro V u ⟨W', w', v, hv, rfl⟩
  have h1 := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv
  exact ⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩

end GlobalTheory.EtC.Tr
end
end

