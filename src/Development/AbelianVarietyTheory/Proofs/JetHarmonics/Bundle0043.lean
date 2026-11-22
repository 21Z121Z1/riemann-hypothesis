import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsoMultiplicative
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOne

theorem exists_root_tower (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ IsPrimitiveRoot (ζ 1) p ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
      ∀ n, ζ n ^ p ^ n = 1 := by
  have hp0 : 0 < p := hp.out.pos
  have : NeZero p := ⟨hp0.ne'⟩
  obtain ⟨z, hz⟩ : ∃ z : K, IsPrimitiveRoot z p := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp0
  have h : ∀ n, (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) (n + 1) ^ p
      = (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) n := by
    intro n
    cases n with
    | zero => exact hz.pow_eq_one
    | succ m =>
      show (r^[m + 1] z) ^ p = r^[m] z
      rw [Function.iterate_succ_apply', hr]
  refine ⟨fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z, rfl, hz, h, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, h n]; exact ih

theorem norm_le_pow_of_primitive {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z p) :
    ‖(p : K)‖ ≤ ‖z - 1‖ ^ (p - 1) := by
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h
  have hle : ∀ j : ℕ, ‖1 - z ^ j‖ ≤ ‖z - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : 1 - z ^ (j + 1) = (1 - z ^ j) + -(z ^ j * (z - 1)) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [norm_neg, norm_mul, norm_pow, hz1, one_pow, one_mul]
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have h := hz.prod_one_sub_pow_eq_order
  have h2 : ((m + 1 : ℕ) : K) = ∏ k ∈ Finset.range m, (1 - z ^ (k + 1)) := by
    rw [h]; push_cast; ring
  rw [h2, norm_prod, Nat.add_sub_cancel]
  calc ∏ k ∈ Finset.range m, ‖1 - z ^ (k + 1)‖ ≤ ∏ _k ∈ Finset.range m, ‖z - 1‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hle _)
    _ = _ := by simp

theorem exists_iso_multiplicative (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (h1 : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (h2 : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ f : PowerSeries K, Intg f ∧ PowerSeries.constantCoeff f = 0 ∧ ‖PowerSeries.coeff 1 f‖ = 1 ∧
      f.subst F.toPowerSeries = f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
          f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  classical
  obtain ⟨t, ht1, ht0, htne, htp⟩ := GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower K p F hF h1 h2
  obtain ⟨ζ, hζ0, hζ1, hζp, hζn⟩ := exists_root_tower K p
  obtain ⟨-, hpt⟩ := GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF
  obtain ⟨ho1, -, ho3⟩ := GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht1 ht0 htne htp
  obtain ⟨hn1, hn2, hn3, hn4⟩ := GlobalTheory.T.norm_formalGroup_heightOne_torsion_tower K p F hF h1 h2 t ht1 ht0 htne htp
  choose g hgI hgv using fun n => GlobalTheory.T.exists_integral_polynomial_torsion_character_level K p F hF t ht1 ht0 htne htp n (ζ n) (hζn n)
  obtain ⟨bI, -, bP, bC, bX, -, -, bS, -, bf⟩ := GlobalTheory.BddAlg.bdd_alg K (Fin 2)
  obtain ⟨bI1, -, bP1, bC1, -⟩ := GlobalTheory.BddAlg.bdd_alg K Unit
  set P : ℕ → ℕ → K := fun n j => ev1 (nMul F j) (t n) with hP
  have hP0 : ∀ n, P n 0 = 0 := fun n => (hpt _ (ht1 n)).1
  have hPlt : ∀ n j, ‖P n j‖ < 1 := fun n j =>
    (((hpt _ (ht1 n)).2.2.1 j).1).trans_lt (ht1 n)
  set G : ℕ → Finset K := fun n => (Finset.Ico 1 (p ^ n)).image (P n) with hG
  have hpn : ∀ n, 0 < p ^ n := fun n => pow_pos hp.out.pos n
  have hmem : ∀ n x, x ∈ G n ↔ ∃ j, ¬ p ^ n ∣ j ∧ P n j = x := by
    intro n x
    simp only [hG, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨j, Nat.not_dvd_of_pos_of_lt hj1 hj2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j % p ^ n, ⟨?_, Nat.mod_lt _ (hpn n)⟩, (ho3 n _ _).2 (Nat.mod_modEq _ _)⟩
      exact Nat.pos_of_ne_zero fun h => hj (Nat.dvd_of_mod_eq_zero h)
  have hmono : Monotone G := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    refine (hmem _ _).2 ⟨p * j, fun h => hj ?_, ho1 n j⟩
    rw [pow_succ'] at h
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h
  have hr0 : 0 < ‖t 1‖ := norm_pos_iff.2 htne
  have hGr : ∀ n, ∀ x ∈ G n, ‖t 1‖ ≤ ‖x‖ ∧ ‖x‖ < 1 := by
    intro n x hx
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    exact ⟨hn3 n j hj, hPlt n j⟩
  have hlim : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) := by
    have : (fun n => ∏ x ∈ G n, ‖x‖) = fun n => ‖(p : K)‖ ^ n := by
      funext n
      rw [← hn4 n, hG]
      refine Finset.prod_image ?_
      intro i hi j hj hij
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      exact Nat.ModEq.eq_of_lt_of_lt ((ho3 n i j).1 hij) hi.2 hj.2
    rw [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hn2
  have hgev : ∀ n m j k, P m k = P n j → ev1 (g m : PowerSeries K) (P n j) = ζ m ^ k := by
    intro n m j k h
    rw [((GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (hPlt n j)).2.2.2.2.1 (g m)).2, ← h]
    exact hgv m k
  obtain ⟨φ, hφI, hφc, hφv⟩ := GlobalTheory.T.exists_limit_powerSeries_agree_on_annulus_points K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim
    (fun n => (g n : PowerSeries K))
    (fun n => (bf _).1.2 fun k => by rw [Polynomial.coeff_coe]; exact hgI n k)
    (by
      intro n x hx
      obtain ⟨j, -, rfl⟩ := (hmem n x).1 hx
      rw [hgev n (n + 1) j (p * j) (ho1 n j), hgev n n j j rfl, pow_mul, hζp])
  have hφ0 : PowerSeries.coeff 0 φ = 1 := by
    have h := hφc 0
    have : (fun n => PowerSeries.coeff 0 (g n : PowerSeries K)) = fun _ => (1 : K) := by
      funext n
      have h3 := hgv n 0
      change (g n).eval (P n 0) = _ at h3
      rw [hP0, pow_zero] at h3
      rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, h3]
    rw [this] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hz : ‖(0 : K)‖ < 1 := by simp
  have hφP : ∀ n j, ev1 φ (P n j) = ζ n ^ j := by
    intro n j
    by_cases hj : p ^ n ∣ j
    · have : P n j = 0 := by
        rw [← hP0 n]
        exact (ho3 n _ _).2 ((Nat.modEq_zero_iff_dvd).2 hj)
      rw [this, (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K 0 hz).2.2.2.2.2.2.2.2.2.2 φ, hφ0]
      obtain ⟨c, rfl⟩ := hj
      rw [pow_mul, hζn, one_pow]
    · rw [hφv n _ ((hmem _ _).2 ⟨j, hj, rfl⟩)]
      exact hgev n n j j rfl
  have hC1 : Intg (PowerSeries.C (1 : K) : PowerSeries K) := (bC1 1).2.1 (by simp)
  set f : PowerSeries K := φ - PowerSeries.C 1 with hf
  have hfI : Intg f := (bI1 _ _ hφI hC1).2.1
  have hfB : Bdd f := (bP1 _ 0).2.2 hfI
  have hf0 : PowerSeries.coeff 0 f = 0 := by
    rw [hf, map_sub, hφ0]; simp
  have hfP : ∀ n j, ev1 f (P n j) = ζ n ^ j - 1 := by
    intro n j
    have h := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (hPlt n j)
    rw [hf, (h.2.1 φ _ ((bP1 _ 0).2.2 hφI) ((bP1 _ 0).2.2 hC1)).2.1, h.2.2.1, hφP]
  refine ⟨f, hfI, by simpa using hf0, ?_, ?_⟩
  · by_contra hne
    have hlt : ‖PowerSeries.coeff 1 f‖ < 1 := lt_of_le_of_ne ((bf f).1.1 hfI 1) hne
    have hv : ev1 f (t 1) = ζ 1 - 1 := by
      have h := hfP 1 1
      rw [pow_one] at h
      rw [← h]
      congr 1
      exact ((hpt _ (ht1 1)).2.1).symm
    have he := ((GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K _ (ht1 1)).2.2.2.2.2.2.1 f hfI).2.2
    rw [hv, hf0, sub_zero] at he
    have hlt2 : ‖ζ 1 - 1‖ < ‖t 1‖ := by
      have : ζ 1 - 1 = (ζ 1 - 1 - PowerSeries.coeff 1 f * t 1) + PowerSeries.coeff 1 f * t 1 := by
        ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (he.trans_lt ?_) ?_)
      · have := ht1 1
        nlinarith
      · rw [norm_mul]
        nlinarith
    have h3 := norm_le_pow_of_primitive hp.out hζ1
    have h4 : ‖ζ 1 - 1‖ ^ (p - 1) < ‖t 1‖ ^ (p - 1) :=
      pow_lt_pow_left₀ hlt2 (norm_nonneg _) (Nat.sub_ne_zero_of_lt hp.out.one_lt)
    linarith
  · have hF0 : MvPowerSeries.constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
    have hX : ∀ i : Fin 2, Intg (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => (bX i).1
    have hX0 : ∀ i : Fin 2,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X i
    have iF := (bS _ f hF hF0).1 hfI
    have i0 := (bS _ f (hX 0) (hX0 0)).1 hfI
    have i1 := (bS _ f (hX 1) (hX0 1)).1 hfI
    have i01 := (bI _ _ i0 i1).1
    have i01' := (bI _ _ i0 i1).2.2
    have iR := (bI _ _ i01 i01').1
    have bd : ∀ S : MvPowerSeries (Fin 2) K, Intg S → Bdd S := fun S h => (bP S 0).2.2 h
    rw [← sub_eq_zero]
    refine GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim _ (bI _ _ iF iR).2.1 ?_
    intro n x hx y hy
    obtain ⟨i, -, rfl⟩ := (hmem n x).1 hx
    obtain ⟨j, -, rfl⟩ := (hmem n y).1 hy
    obtain ⟨-, eA, -, eX, -, -, -, eS⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K (Fin 2) ![P n i, P n j]
      (Fin.forall_fin_two.2 ⟨hPlt n i, hPlt n j⟩)
    have hs : ev F.toPowerSeries ![P n i, P n j] = P n (i + j) := (hpt _ (ht1 n)).2.2.2.1 i j
    rw [(eA _ _ (bd _ iF) (bd _ iR)).2.1, (eA _ _ (bd _ i01) (bd _ i01')).1,
      (eA _ _ (bd _ i0) (bd _ i1)).1, (eA _ _ (bd _ i0) (bd _ i1)).2.2,
      eS _ f hF hF0 hfB, eS _ f (hX 0) (hX0 0) hfB, eS _ f (hX 1) (hX0 1) hfB, eX, eX, hs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfP, hfP, hfP]
    ring

end GlobalTheory.ConvSer.HeightOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation
section
namespace GlobalTheory

open scoped NNReal

noncomputable def expNegTop : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => ⟨Real.exp (-(q : ℝ)), (Real.exp_pos _).le⟩

@[simp] theorem expNegTop_top : expNegTop ⊤ = 0 := rfl

theorem expNegTop_coe (q : ℚ) : ((expNegTop (q : WithTop ℚ) : ℝ≥0) : ℝ) = Real.exp (-(q : ℝ)) := rfl

theorem expNegTop_zero : expNegTop 0 = 1 := by
  apply NNReal.coe_injective
  have h := expNegTop_coe 0
  simpa using h

theorem expNegTop_add (a b : WithTop ℚ) : expNegTop (a + b) = expNegTop a * expNegTop b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      apply NNReal.coe_injective
      rw [← WithTop.coe_add, NNReal.coe_mul, expNegTop_coe, expNegTop_coe, expNegTop_coe,
        ← Real.exp_add]
      push_cast
      ring_nf

theorem expNegTop_le_iff (a b : WithTop ℚ) : expNegTop a ≤ expNegTop b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [← NNReal.coe_le_coe, expNegTop_coe]
      simp only [expNegTop_top, NNReal.coe_zero, top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact Real.exp_pos _
    | coe b =>
      rw [← NNReal.coe_le_coe, expNegTop_coe, expNegTop_coe, Real.exp_le_exp, neg_le_neg_iff,
        Rat.cast_le, WithTop.coe_le_coe]

noncomputable def expNegValuation {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    Valuation F ℝ≥0 where
  toFun x := expNegTop (v x)
  map_zero' := by simp
  map_one' := by simp [expNegTop_zero]
  map_mul' x y := by rw [v.map_mul, expNegTop_add]
  map_add_le_max' x y := by
    rcases min_le_iff.mp (v.map_add x y) with h | h
    · exact le_max_of_le_left ((expNegTop_le_iff _ _).mpr h)
    · exact le_max_of_le_right ((expNegTop_le_iff _ _).mpr h)

theorem expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl

theorem expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]

theorem exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeTateImage

open GlobalTheory.TangentPow GlobalTheory.GmPoints

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}

noncomputable def bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    specO O (DualNumber R) ⟶ G :=
  ptMap (dualBC (Algebra.ofId O R)) ≫ x.1

theorem fst_bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ bc R x = 1 := by
  have h : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (dualBC (Algebra.ofId O R)) =
      ptMap (Algebra.ofId O R) ≫ ptMap (TrivSqZeroExt.fstHom O O O) := by
    rw [ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  rw [bc, ← Category.assoc, h, Category.assoc, x.2]
  exact comp_one _

theorem dualBC_fst {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).fst = φ y.fst := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem dualBC_snd {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).snd = φ y.snd := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem ptMap_bc {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (x : LieG G) : ptMap (dualBC φ) ≫ bc R x = bc R' x := by
  rw [bc, bc, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun y => ?_
  ext
  · simp only [AlgHom.comp_apply, dualBC_fst, Algebra.ofId_apply, AlgHom.commutes]
  · simp only [AlgHom.comp_apply, dualBC_snd, Algebra.ofId_apply, AlgHom.commutes]

theorem existsUnique_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : ∃! w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
      w ≫ torsion.ι G (p ^ n) = bc R x :=
  (pow_eq_scale_and_existsUnique_torsion O G R (p ^ n) _ (fst_bc R x)).2 (by exact_mod_cast hR)

noncomputable def lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : specO O (DualNumber R) ⟶ torsion G (p ^ n) :=
  (existsUnique_lift hR x).choose

theorem lift_ι {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : lift hR x ≫ torsion.ι G (p ^ n) = bc R x :=
  (existsUnique_lift hR x).choose_spec.1

theorem eq_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) {w : specO O (DualNumber R) ⟶ torsion G (p ^ n)}
    (hw : w ≫ torsion.ι G (p ^ n) = bc R x) : w = lift hR x :=
  (existsUnique_lift hR x).unique hw (lift_ι hR x)

variable (χ : Tv G p)

noncomputable def unitAt {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : DualNumber R :=
  (unitOf (lift hR x ≫ χ.χ n) : DualNumber R)

theorem unitAt_fst {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : (unitAt χ hR x).fst = 1 := by
  set z := ptMap (TrivSqZeroExt.fstHom O R R) ≫ lift hR x with hz
  have h1 : z ≫ torsion.ι G (p ^ n) = 1 := by
    rw [hz, Category.assoc, lift_ι, fst_bc]
  have h2 := χ.isChar n _ z z z (by rw [h1, _root_.mul_one])
  have h3 : unitOf (z ≫ χ.χ n) = 1 := by
    have := congrArg unitOf h2
    rw [unitOf_mul] at this
    exact left_eq_mul.mp this
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O R R) (lift hR x ≫ χ.χ n)
  rw [← Category.assoc, ← hz, h3] at h4
  exact h4.symm

theorem unitAt_map {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (hR : (p : R) ^ n = 0) (hR' : (p : R') ^ n = 0) (x : LieG G) :
    (unitAt χ hR' x).snd = φ (unitAt χ hR x).snd := by
  have h : ptMap (dualBC φ) ≫ lift hR x = lift hR' x :=
    eq_lift hR' x (by rw [Category.assoc, lift_ι, ptMap_bc])
  rw [unitAt, ← h, Category.assoc, unitOf_ptMap, dualBC_snd, unitAt]

theorem unitAt_le {m n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hm : (p : R) ^ m = 0)
    (hmn : m ≤ n) (hn : (p : R) ^ n = 0) (x : LieG G) : unitAt χ hn x = unitAt χ hm x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn' : (p : R) ^ n = 0 := pow_eq_zero_of_le hmn hm
    rw [← ih hn', unitAt, unitAt,
      χ.compat n _ (lift hn' x) (lift hn x) (by rw [lift_ι, lift_ι])]

theorem unitAt_mul {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x y z : LieG G) (h : z.1 = x.1 * y.1) :
    (unitAt χ hR z).snd = (unitAt χ hR x).snd + (unitAt χ hR y).snd := by
  have h1 := χ.isChar n _ (lift hR x) (lift hR y) (lift hR z)
    (by rw [lift_ι, lift_ι, lift_ι, bc, bc, bc, h, comp_mul])
  have h2 : unitAt χ hR z = unitAt χ hR x * unitAt χ hR y := by
    rw [unitAt, h1, unitOf_mul, Units.val_mul, unitAt, unitAt]
  rw [h2, DualNumber.snd_mul, unitAt_fst, unitAt_fst]
  ring

theorem unitAt_scale {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (a : O) (x z : LieG G) (h : z.1 = ptMap (dualScale a) ≫ x.1) :
    (unitAt χ hR z).snd = algebraMap O R a * (unitAt χ hR x).snd := by
  have h1 : scale O (algebraMap O R a) ≫ lift hR x = lift hR z := by
    refine eq_lift hR z ?_
    rw [Category.assoc, lift_ι, bc, bc, h, ← Category.assoc, ← Category.assoc, scale,
      ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 2
    refine AlgHom.ext fun y => ?_
    ext
    · simp [dualBC_fst, dualScale]
    · simp [dualBC_snd, dualScale, Algebra.smul_def]
  rw [unitAt, ← h1, Category.assoc, scale, unitOf_ptMap]
  simp [unitAt, Algebra.smul_def]

theorem pow_quot (n : ℕ) : (p : O ⧸ Ideal.span {(p : O) ^ n}) ^ n = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p : O) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_natCast] at this

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]

theorem eq_of_forall [IsHausdorff (Ideal.span {(p : O)}) O] {a b : O}
    (h : ∀ n, algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : O)}) (a - b) fun n => ?_)
  rw [SModEq.zero, ← SModEq.sub_mem, smod_iff]
  exact h n

theorem exists_level (n : ℕ) (x : LieG G) : ∃ a : O, ∀ (R : Type) [CommRing R] [Algebra O R]
    (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unitAt χ (pow_quot (O := O) n) x).snd
  refine ⟨a, fun R _ _ hR => ?_⟩
  let φ : (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] R :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId O R) fun c hc => by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hR]
  rw [unitAt_map χ φ (pow_quot n) hR, ← ha]
  exact (φ.commutes a).symm

theorem exists_limit [IsPrecomplete (Ideal.span {(p : O)}) O] (x : LieG G) :
    ∃ a : O, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R]
      (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  choose a ha using fun n => exists_level χ n x
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) a fun {m n} hmn => by
    rw [smod_iff, ha m _ (pow_quot m), ha n _ (pow_eq_zero_of_le hmn (pow_quot m)),
      unitAt_le χ (pow_quot m) hmn]
  refine ⟨L, fun n R _ _ hR => ?_⟩
  have h := hL n
  rw [smod_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at h
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  rw [← ha n R hR, eq_comm, ← sub_eq_zero, ← map_sub, ← hd]
  simp [hR]

theorem isAl_iff (f : LieG G → O) : IsAl χ f ↔ ∀ (x : LieG G) (n : ℕ) (R : Type) [CommRing R]
    [Algebra O R] (hR : (p : R) ^ n = 0), algebraMap O R (f x) = (unitAt χ hR x).snd := by
  constructor
  · intro h x n R _ _ hR
    rw [unitAt, h n R hR x _ (lift_ι hR x), TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  · intro h n R _ _ hR x w hw
    rw [eq_lift hR x hw]
    ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact unitAt_fst χ hR x
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact (h x n R hR).symm

theorem existsUnique_isAl [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f := by
  choose f hf using exists_limit χ
  refine ⟨f, ⟨⟨fun x y h => eq_of_forall (p := p) fun n => ?_,
    fun a x h => eq_of_forall (p := p) fun n => ?_⟩, (isAl_iff χ f).2 hf⟩, fun g hg => ?_⟩
  · rw [map_add, hf x n _ (pow_quot n), hf y n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_mul χ _ x y _ rfl)
  · rw [map_mul, hf x n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_scale χ _ a x _ rfl)
  · funext x
    refine eq_of_forall (p := p) fun n => ?_
    rw [hf _ n _ (pow_quot n), (isAl_iff χ g).1 hg.2 x n _ (pow_quot n)]

end GlobalTheory.HodgeTateImage
end

