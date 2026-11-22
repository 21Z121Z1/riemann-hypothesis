import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSnapperSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSpecialCurves
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem rename_mem_mIdealOver (S : Type) [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) S}
    (hf : f ∈ mIdealOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) :
    rename (fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) f ∈ mIdealOver S y := by
  subst hx
  have hcomp : (mConeMapOver S y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars S).comp
        (mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem specialIdeal_le_baseComap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [DecidableEq K] {ι : K → Type} {Ω : Type}
    [Field Ω] [Algebra O Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    {x : Fin (N + 1) → Ω} (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    {W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O))}
    (hW : NumbersDVR.specialIdeal (mIdealOver O y) ≤ W) :
    NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤
      baseComap (IsLocalRing.ResidueField O) k₀ e W := by
  rw [NumbersDVR.specialIdeal, Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, baseComap, Ideal.mem_comap, ← map_rename]
  exact hW (Ideal.mem_map_of_mem _ (rename_mem_mIdealOver O y k₀ e hx hf))

theorem SpecialCurves.proof (hdim : SpecialCurvesDim.Statement) (hlift : SpecialCurvesLift.Statement) :
    SpecialCurves.Statement := by
  intro O _ _ _ K _ _ ι _ Ω _ _ _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap _ k₀ e hW,
    specialIdeal_le_baseComap O y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim O K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift O K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim O K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleHilbert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

namespace VeryAmpleHilbert

theorem exists_slice (Q : MvPolynomial (Fin 2) ℚ) (e : ℕ) (hQ : Q.totalDegree ≤ e) (c : ℚ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ e ∧ p.coeff e = Q.coeff (Finsupp.single 0 e) ∧
      ∀ a : ℚ, p.eval a = MvPolynomial.eval ![a, c] Q := by
  have hdeg : ∀ m ∈ Q.support, m 0 + m 1 ≤ e := fun m hm => by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  refine ⟨∑ m ∈ Q.support, Polynomial.C (Q.coeff m * c ^ m 1) * Polynomial.X ^ m 0, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := hdeg m hm
    omega
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 e)]
    · simp
    · intro m hm hne
      rw [if_neg]
      intro hme
      apply hne
      have := hdeg m hm
      ext i
      fin_cases i
      · simp [hme]
      · simp
        omega
    · intro h
      rw [MvPolynomial.notMem_support_iff.mp h]
      simp
  · intro a
    rw [Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem fwdDiff_iter_eval (p : Polynomial ℚ) (e : ℕ) (hp : p.natDegree ≤ e) (y : ℚ) :
    (fwdDiff 1)^[e] p.eval y = e.factorial * p.coeff e := by
  rcases hp.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rw [Polynomial.leadingCoeff, mul_comm]

theorem sum_subsets_eq_fwdDiff (e : ℕ) (f : ℚ → ℚ) :
    ∑ T : Finset (Fin e), (-1 : ℚ) ^ (e - T.card) * f T.card = (fwdDiff 1)^[e] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun m => (-1 : ℚ) ^ (e - m) * f m), Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_const (Q : SubSystem k x Ω) {n : ℕ} (l : List (Fin n)) (m : ℕ) :
    l.foldl (fun F _ => F.twist Q) (Q.pow m) = Q.pow (m + l.length) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    change l.foldl _ (Q.pow (m + 1)) = _
    rw [ih]
    congr 1
    omega

theorem tensorSub_const (Q : SubSystem k x Ω) {n : ℕ} (T : Finset (Fin n)) :
    tensorSub (fun _ : Fin n => Q) T = Q.pow T.card := by
  have h := foldl_twist_const Q ((List.finRange n).filter (· ∈ T)) 0
  rw [zero_add] at h
  unfold tensorSub
  refine h.trans ?_
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

end VeryAmpleHilbert

open VeryAmpleHilbert in

theorem VeryAmpleHilbert.proof (hS : VeryAmpleSnapper.Statement.{u, w}) : VeryAmpleHilbert.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hN
  obtain ⟨hfin, Q, c₀, hdeg, hQ, hQ0⟩ := hS k Ω N x e Nb hZ hN
  have hpow : ∀ n : ℕ, twistMul Nb.toSubSystem n 0 = Nb.toSubSystem.pow n := fun n =>
    SubSystem.twist_twistSys_zero _
  refine ⟨fun n => hpow n ▸ hfin n 0, ?_⟩
  obtain ⟨P, hPdeg, hPe, hPev⟩ := exists_slice Q e hdeg 0
  refine ⟨P, hPdeg, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hZ.relevant
    have hxj : x j ≠ 0 := fun h0 => hj ((mem_primeOf_of_isHomogeneous x
      (MvPolynomial.isHomogeneous_X k j)).mpr (by rw [MvPolynomial.aeval_X, h0]))
    have hsum : ∀ c : ℕ, c₀ ≤ c → (interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c : ℚ) =
        e.factorial * Q.coeff (Finsupp.single 0 e) := by
      intro c hc
      obtain ⟨p, hpd, hpe, hpv⟩ := exists_slice Q e hdeg c
      rw [← hpe, ← fwdDiff_iter_eval p e hpd 0, funext hpv, ← sum_subsets_eq_fwdDiff, interSum]
      push_cast
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [tensorSub_const, SectionsOverLocalization.restrLen_primeOf_eq_finrank x hxj, Int.cast_natCast]
      congr 1
      have h := hQ T.card c hc
      rw [Int.cast_natCast] at h
      exact h
    set z := interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c₀.toNat
    have hz : ∀ c : ℕ, c₀.toNat ≤ c →
        interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c = z := fun c hc => by
      have h1 := hsum c (by omega)
      rw [← hsum c₀.toNat (by omega)] at h1
      exact_mod_cast h1
    have hlim : interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) = z :=
      (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨c₀.toNat, fun c hc => (hz c hc).symm⟩)).limUnder_eq
    rw [hlim, hsum c₀.toNat (by omega), hPe, mul_comm]
  · filter_upwards [hQ0] with n hn
    rw [hn, hPev]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

theorem relDim_mIdealOver_eq_trdeg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ t : ℕ, Algebra.trdeg F (chartRingOver F y c) = t ∧
      relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  refine ⟨t, ht, ?_⟩
  unfold relDim
  rw [dimy]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

theorem SegreDim.proof : SegreDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y hy
  choose c hc using hy
  obtain ⟨t, ht, hrel⟩ := relDim_mIdealOver_eq_trdeg (F := F) y c hc
  obtain ⟨t', ht', hrel'⟩ := relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c)
    (segreChart_adm y (segreVec_ne_zero y hc) hc)
  have heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c :=
    le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)
  rw [heq, ht] at ht'
  have htt : t = t' := by exact_mod_cast ht'
  rw [hrel, hrel', htt]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RingKrullDimRangeCompAddOneLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim ringKrullDim_eq_of_relDim)

noncomputable section

section RangeDim

variable {F A T T' : Type*} [CommRing F] [CommRing A] [CommRing T] [CommRing T'] [Algebra F A] [Algebra F T]
  [Algebra F T']

def rangeCompMap (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') : φ.range →ₐ[F] (ψ.comp φ).range :=
  (ψ.comp φ.range.val).codRestrict _ (by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩)

theorem rangeCompMap_surjective (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') :
    Function.Surjective (rangeCompMap φ ψ) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨φ a, a, rfl⟩, rfl⟩

theorem ringKrullDim_range_comp_add_one_le [IsDomain T] (φ : A →ₐ[F] T) (ψ : T →ₐ[F] T') (a : A)
    (ha : φ a ≠ 0) (hψ : ψ (φ a) = 0) :
    ringKrullDim (ψ.comp φ).range + 1 ≤ ringKrullDim φ.range := by
  let r : φ.range := ⟨φ a, a, rfl⟩
  have hr : r ∈ nonZeroDivisors φ.range :=
    mem_nonZeroDivisors_of_ne_zero fun h => ha (congrArg Subtype.val h)
  let χ := (rangeCompMap φ ψ).toRingHom
  have hχr : ∀ b ∈ Ideal.span {r}, χ b = 0 := by
    intro b hb
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [map_mul]
    have : χ r = 0 := Subtype.ext hψ
    rw [this, mul_zero]
  have h1 := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hχr (rangeCompMap_surjective φ ψ))
  exact (add_le_add h1 le_rfl).trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)

end RangeDim

section Chart

variable {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra F Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)

def partDehom (s : Finset K) : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K Ω :=
  aeval fun p => if p.1 ∈ s then C (y p / y ⟨p.1, c p.1⟩) else C (y p) * X p.1

def subst1 (k : K) : MvPolynomial K Ω →ₐ[F] MvPolynomial K Ω :=
  (aeval fun j => if j = k then C (y ⟨k, c k⟩)⁻¹ else X j : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars F

theorem subst1_comp {s : Finset K} {k : K} (hk : k ∉ s) :
    (subst1 (F := F) y c k).comp (partDehom y c s) = partDehom y c (insert k s) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, i⟩
  simp only [partDehom, subst1, AlgHom.comp_apply, aeval_X, Finset.mem_insert]
  by_cases hj : j ∈ s
  · have : j ≠ k := fun h => hk (h ▸ hj)
    simp [hj]
  · by_cases hjk : j = k
    · subst hjk
      simp only [hj, if_false, if_true, AlgHom.restrictScalars_apply, map_mul, aeval_C, aeval_X]
      rw [div_eq_mul_inv, C_mul]
      simp
    · simp [hj, hjk]

theorem partDehom_empty : partDehom (F := F) y c ∅ = mConeMapOver F y := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [partDehom, mConeMapOver]

theorem ringKrullDim_partDehom_insert (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Finset K} {k : K} (hk : k ∉ s) :
    ringKrullDim (partDehom (F := F) y c (insert k s)).range + 1 ≤ ringKrullDim (partDehom (F := F) y c s).range := by
  have key := ringKrullDim_range_comp_add_one_le (partDehom (F := F) y c s) (subst1 y c k) (X ⟨k, c k⟩ - 1) ?_ ?_
  · rwa [subst1_comp y c hk] at key
  · intro h
    have h' := congrArg constantCoeff h
    simp [partDehom, hk] at h'
  · rw [← AlgHom.comp_apply, subst1_comp y c hk]
    simp [partDehom, hc k]

theorem chartRingOver_eq_range [Fintype K] :
    chartRingOver F y c = (((aeval fun _ => (0 : Ω) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars F).comp
      (partDehom (F := F) y c Finset.univ)).range := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp [partDehom]

end Chart

theorem le_zero_of_add_natCast_le {d : WithBot ℕ∞} {n : ℕ} (h : d + n ≤ n) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe e =>
      have h' : ((e + n : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : e + n ≤ n := by exact_mod_cast h'
      have : e = 0 := by omega
      subst this
      simp

theorem PointChartField.full : PointChartField.Statement := by
  intro F _ K _ _ ι Ω _ _ y hdim c hc
  have h0 : ringKrullDim (partDehom (F := F) y c ∅).range = (Fintype.card K : WithBot ℕ∞) := by
    rw [partDehom_empty, ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange _).toRingEquiv]
    have := ringKrullDim_eq_of_relDim (Q := mIdealOver F y) (m := 0) hdim
    rw [Nat.zero_add] at this
    exact this
  have hstep : ∀ s : Finset K,
      ringKrullDim (partDehom (F := F) y c s).range + (s.card : WithBot ℕ∞) ≤ Fintype.card K := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert k s hk ih =>
      rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_comm ((s.card : ℕ) : WithBot ℕ∞) 1,
        ← add_assoc]
      exact (add_le_add (ringKrullDim_partDehom_insert y c hc hk) le_rfl).trans ih
  have hu := hstep Finset.univ
  rw [Finset.card_univ] at hu
  have hle : ringKrullDim (chartRingOver F y c) ≤ 0 := by
    rw [chartRingOver_eq_range]
    exact (ringKrullDim_le_of_surjective _ (rangeCompMap_surjective _ _)).trans (le_zero_of_add_natCast_le hu)
  have : Ring.KrullDimLE 0 (chartRingOver F y c) := Ring.krullDimLE_iff.mpr (by simpa using hle)
  exact Ring.KrullDimLE.isField_of_isDomain

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftMapMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => Polynomial.coeff p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

