import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ShiftedSumMemTypicalCurveSet
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPow
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChF

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.Regauge

variable {R : Type} [CommRing R] {d : ℕ}

private theorem gp_mulF (F : FGLaw R d) (N : ℕ) : GP (mulF F.F N) :=
  FormalMul.constantCoeff_mulF F.F F.const N

private theorem nsum_add (F : FGLaw R d) (a b : ℕ) :
    mulF F.F (a + b) = addOf F.F (mulF F.F a) (mulF F.F b) := by
  induction b with
  | zero => exact (addOf_zero F (gp_mulF F a)).symm
  | succ b ih =>
    change addOf F.F (mulF F.F (a + b)) (pt R d 0) = addOf F.F _ (addOf F.F (mulF F.F b) (pt R d 0))
    rw [ih, addOf_assoc F (gp_mulF F a) (gp_mulF F b) (gp_pt 0)]

private theorem nsum_mul (F : FGLaw R d) (N M : ℕ) :
    mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M) := by
  have hV := single_point_zero_constant (gp_mulF F M)
  induction N with
  | zero =>
    rw [Nat.zero_mul]
    exact (evP_zero _ hV).symm
  | succ N ih =>
    rw [Nat.succ_mul, nsum_add, ih]
    change _ = evP ![mulF F.F M] (addOf F.F (mulF F.F N) (pt R d 0))
    rw [evP_addOf _ hV _ _ _ (gp_mulF F N) (gp_pt 0), evP_pt _ hV]
    rfl

private theorem ev_mem_pow {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {K : Ideal (PS R n d)} (hK : ∀ j i, a j i ∈ K) {N : ℕ} {f : PS R m d}
    (hf : f ∈ germIdeal (Fin m × Fin d) R ^ N) : ev a f ∈ K ^ N := by
  have h : (germIdeal (Fin m × Fin d) R ^ N).map (substAlgHom (R := R) (gt_hasSubst a ha)) ≤ K ^ N := by
    rw [Ideal.map_pow, germIdeal_eq_span]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [substAlgHom_X]
    exact hK _ _
  have := h (Ideal.mem_map_of_mem _ hf)
  rwa [substAlgHom_apply] at this

private theorem mem_sq_iff {σ : Type} [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ 2 ↔ constantCoeff g = 0 ∧ ∀ s, coeff (Finsupp.single s 1) g = 0 := by
  rw [mem_germIdeal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun s => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ e he
    rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
    · obtain rfl := (Finsupp.degree_eq_zero_iff e).1 h
      simpa using h0
    · obtain ⟨s, rfl⟩ : e ∈ Set.range (fun s : σ => Finsupp.single s 1) := by
        rw [Finsupp.range_single_one]; exact h
      exact h1 s

private theorem coeff_single_X' {σ : Type} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  simp [Finsupp.single_left_inj]

private theorem sub_lin_mem {σ : Type} [Fintype σ] {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    g - ∑ s, coeff (Finsupp.single s 1) g • X s ∈ germIdeal σ R ^ 2 := by
  classical
  refine mem_sq_iff.2 ⟨by simp [hg], fun s => ?_⟩
  simp [coeff_single_X']

private theorem ev_sub_lin_mem {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {f : PS R m d} (hf : constantCoeff f = 0) :
    ev a f - ∑ s : Fin m × Fin d, coeff (Finsupp.single s 1) f • a s.1 s.2 ∈
      germIdeal (Fin n × Fin d) R ^ 2 := by
  have h := ev_mem_pow ha (K := germIdeal (Fin n × Fin d) R) (fun j i => ha j i) (sub_lin_mem hf)
  unfold ev at h ⊢
  rw [← substAlgHom_apply (gt_hasSubst a ha)] at h ⊢
  simpa only [map_sub, map_sum, map_smul, substAlgHom_X] using h

private theorem coeff_law (F : FGLaw R d) (i : Fin d) (l : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (l, j) 1) (F.F i) = if j = i then 1 else 0 := by
  have hp : GP (pt R (n := 1) d 0) := gp_pt 0
  fin_cases l
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant hp gp_zero₂) (F.const i))).2 (0, j)
    have e : ev ![pt R (n := 1) d 0, 0] (F.F i) = X (0, i) := congrFun (addOf_zero F hp) i
    rw [e] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant gp_zero₂ hp) (F.const i))).2 (0, j)
    rw [F.unit i] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm

private theorem nsum_sub_mem (F : FGLaw R d) (N : ℕ) (i : Fin d) :
    mulF F.F N i - (N : R) • X (0, i) ∈ germIdeal (Fin 1 × Fin d) R ^ 2 := by
  induction N with
  | zero => simp [mulF]
  | succ N ih =>
    have h := ev_sub_lin_mem (pair_points_zero_constant (gp_mulF F N) (gp_pt 0)) (F.const i)
    simp only [Fintype.sum_prod_type, coeff_law, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert add_mem h ih using 1
    change ev ![mulF F.F N, pt R d 0] (F.F i) - _ = _
    simp only [pt, Nat.cast_succ, add_smul, one_smul]
    abel

private theorem lin_nsum (F : FGLaw R d) (N : ℕ) :
    lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  have h := (mem_sq_iff.1 (nsum_sub_mem F N i)).2 (0, j)
  rw [map_sub, sub_eq_zero, map_smul, coeff_single_X'] at h
  simp [lin, h, Matrix.one_apply, eq_comm]

private theorem span_nsum_le (F : FGLaw R d) (N M : ℕ) :
    Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M)) := by
  rw [Ideal.span_le, nsum_mul]
  rintro _ ⟨j, rfl⟩
  have := ev_mem_pow (single_point_zero_constant (gp_mulF F M)) (K := Ideal.span (Set.range (mulF F.F M))) (N := 1)
    (f := mulF F.F N j) (fun l i => by fin_cases l; exact Ideal.subset_span ⟨i, rfl⟩)
    (by rw [pow_one]; exact gp_mulF F N j)
  rwa [pow_one] at this

private theorem nsum_pow_mem (F : FGLaw R d) (p k : ℕ) (j : Fin d) :
    mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  set J := (Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d)) with hJ
  induction k generalizing j with
  | zero =>
    rw [zero_add, pow_one, hJ, ← germIdeal_eq_span]
    exact Ideal.mem_sup_right (gp_mulF F _ j)
  | succ k ih =>
    have hV := single_point_zero_constant (gp_mulF F (p ^ k))
    have h := ev_mem_pow hV (K := J ^ (k + 1)) (fun l i => by fin_cases l; exact ih i)
      (nsum_sub_mem F p j)
    rw [← pow_mul, gt_ev_sub _ hV, smul_eq_C_mul, gt_ev_mul _ hV, gt_ev_X _ hV] at h
    have h1 := Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) h
    have hC : ev ![mulF F.F (p ^ k)] (C (p : R) : PS R 1 d) = C (p : R) := subst_C _
    have h2 : C (p : R) * mulF F.F (p ^ k) j ∈ J ^ (k + 1 + 1) := by
      rw [pow_succ' J (k + 1)]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.subset_span rfl))) (ih j)
    rw [hC] at h1
    have h3 := add_mem h1 h2
    rw [pow_succ' p k, nsum_mul]
    simpa [comp1] using h3

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF

theorem lin_mulF_and_comp_and_span_le_and_mem_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) :=
  fun _ _ _ F => ⟨lin_nsum F, nsum_mul F, span_nsum_le F, nsum_pow_mem F⟩

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataHodgeTateInclusion
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma smul_mem_span_of_split {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] {g d r m : ℕ}
    (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (Ht : Matrix (Fin g) κ O)
    (s : Fin m → Fin d → O) (cp : O) (hex : SplitEx A B)
    (hB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => Ht l i)) (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1)
    (hsurj : ∀ f : Fin g → O, ∃ t, Ht *ᵥ t = cp • f) (f : Fin d → O) :
    cp • f ∈ Submodule.span O (Set.range s) := by
  obtain ⟨-, A', B', -, -, h1⟩ := hex
  choose k hk using hT
  set u : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with hu
  have huS : u ∈ Submodule.span O (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
  have hAu : Aᵀ *ᵥ u = Aᵀ *ᵥ f := by
    rw [hu, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : Aᵀ *ᵥ (f - u) = 0 := by rw [Matrix.mulVec_sub, hAu, sub_self]
  have h2 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one]
  have h3 : f - u = Bᵀ *ᵥ (B'ᵀ *ᵥ (f - u)) := by
    have := congrArg (fun M => M *ᵥ (f - u)) h2
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec] at this
    exact this.symm
  obtain ⟨t, ht⟩ := hsurj (B'ᵀ *ᵥ (f - u))
  have h4 : cp • (f - u) = Bᵀ *ᵥ (Ht *ᵥ t) := by rw [ht, Matrix.mulVec_smul, ← h3]
  have h5 : Ht *ᵥ t = ∑ i, t i • (fun l => Ht l i) := by
    ext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h6 : cp • (f - u) ∈ Submodule.span O (Set.range s) := by
    rw [h4, h5, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    obtain ⟨j, hj⟩ := hB i
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj⟩)
  have h7 : cp • f = cp • (f - u) + cp • u := by rw [← smul_add, sub_add_cancel]
  rw [h7]
  exact Submodule.add_mem _ h6 (Submodule.smul_mem _ _ huS)

theorem linDat_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL c hc f
  have := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsurj := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt
  have hle : v (algebraMap O C c) ≤ v (algebraMap O C cp) := by
    rw [← hS.cp_val] at hc
    exact le_of_pow_le_pow_left₀ (by have := (Fact.out : p.Prime).two_le; omega) zero_le hc
  obtain ⟨e, rfl⟩ := hv.dvd_of_le hle
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _
    (smul_mem_span_of_split A B H.Ht s cp hL.exact hL.fromB hL.fromT hsurj f)

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeight
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm
  simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUniqueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_algebra_of_isAdicComplete_matrix_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O], Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ) (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]), f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  first | exact @GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | exact GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique | (intros; apply GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ShiftedSumMemTypicalCurveSetStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedSum_mem_typicalCurveSet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (y : ℕ → ℕ → I g ⊕ JJ I g → C), (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g := by
  first | exact @GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet | exact GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet | (intros; apply GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem squarefree_map_minpoly_int (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Finite ℤ OE] (a : OE) :
    Squarefree ((minpoly ℤ a).map (Int.castRingHom C)) := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : Irreducible (minpoly ℤ a) := minpoly.irreducible hi
  have h2 : Irreducible ((minpoly ℤ a).map (algebraMap ℤ ℚ)) :=
    ((minpoly.monic hi).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp h1
  have h3 := (h2.separable.map (f := algebraMap ℚ C)).squarefree
  rw [Polynomial.map_map] at h3
  have h4 : (algebraMap ℚ C).comp (algebraMap ℤ ℚ) = Int.castRingHom C := RingHom.ext_int _ _
  rwa [h4] at h3

private theorem aeval_map_minpoly_int (C : Type) [Field C] (OE : Type)
    [CommRing OE] (A : Type) [Ring A] [Algebra C A] (ρ : OE →+* A) (a : OE) :
    Polynomial.aeval (ρ a) ((minpoly ℤ a).map (Int.castRingHom C)) = 0 := by
  have h4 : Int.castRingHom C = algebraMap ℤ C := RingHom.ext_int _ _
  rw [h4, Polynomial.aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at this
  exact this

private theorem finite_ringHom_order (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    Finite (OE →+* C) := by
  classical
  let b := Module.Free.chooseBasis ℤ OE
  let p : OE → Polynomial C := fun a => (minpoly ℤ a).map (Int.castRingHom C)
  have hfin : ∀ a, Finite ((p a).rootSet C) := fun a => (Polynomial.rootSet_finite _ _).to_subtype
  let F : (OE →+* C) → ∀ i, (p (b i)).rootSet C := fun τ i =>
    ⟨τ (b i), Polynomial.mem_rootSet.mpr
      ⟨(squarefree_map_minpoly_int C OE (b i)).ne_zero, aeval_map_minpoly_int C OE C τ (b i)⟩⟩
  refine Finite.of_injective F fun τ σ h => ?_
  have : τ.toAddMonoidHom.toIntLinearMap = σ.toAddMonoidHom.toIntLinearMap :=
    b.ext fun i => congrArg Subtype.val (congrFun h i)
  exact RingHom.ext fun a => LinearMap.congr_fun this a

private theorem mem_iSup_of_eigenvector (C : Type) [Field C] (OE : Type) [CommRing OE]
    (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V) (χ : OE → C) (x : V)
    (hx : ∀ a, ρ a x = χ a • x) :
    x ∈ ⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a) := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hinj : Function.Injective fun c : C => c • x := smul_left_injective C h0
  let τ : OE →+* C :=
    { toFun := χ
      map_one' := hinj (by simp only [← hx, map_one, one_smul, Module.End.one_apply])
      map_mul' := fun a b => hinj (by
        simp only
        rw [← hx, map_mul, Module.End.mul_apply, hx b, map_smul, hx a, smul_smul, mul_comm])
      map_zero' := hinj (by simp only [← hx, map_zero, zero_smul, LinearMap.zero_apply])
      map_add' := fun a b => hinj (by
        simp only
        rw [← hx, map_add, LinearMap.add_apply, hx a, hx b, add_smul]) }
  refine Submodule.mem_iSup_of_mem τ ((Submodule.mem_iInf _).mpr fun a => ?_)
  exact Module.End.mem_eigenspace_iff.mpr (hx a)

theorem order_rep_diagonalisable : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], Finite (OE →+* C) ∧ ∀ (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V), iSupIndep (fun τ : OE →+* C => ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) ∧ (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) = ⊤ := by
  intro C _ _ _ OE _ _ _ _ _
  refine ⟨finite_ringHom_order C OE, fun V _ _ ρ => ⟨?_, ?_⟩⟩
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : OE => ρ a)
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
    have h2 := h.comp (f := fun τ : OE →+* C => (τ : OE → C)) DFunLike.coe_injective
    refine h2.mono fun τ => ?_
    exact iInf_mono fun a => (Module.End.genEigenspace (ρ a) (τ a)).mono le_top
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have hss : ∀ a, (ρ a).IsSemisimple := fun a =>
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero (squarefree_map_minpoly_int C OE a)
        (aeval_map_minpoly_int C OE _ ρ a)
    rw [eq_top_iff]
    rintro v -
    let W : Submodule C V := Submodule.span C (Set.range fun a : OE => ρ a v)
    have hW : ∀ a, W ∈ (ρ a).invtSubmodule := by
      intro a
      rw [Module.End.mem_invtSubmodule, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine Submodule.subset_span ⟨a * b, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    have hfin : FiniteDimensional C W := by
      let b := Module.Free.chooseBasis ℤ OE
      have hle : W ≤ Submodule.span C (Set.range fun i => ρ (b i) v) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
        simp only [SetLike.mem_coe]
        induction ha using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply]
          exact Submodule.add_mem _ hx hy
        | smul n x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply]
          exact zsmul_mem hx n
      have : FiniteDimensional C (Submodule.span C (Set.range fun i => ρ (b i) v)) :=
        FiniteDimensional.span_of_finite C (Set.finite_range _)
      exact Submodule.finiteDimensional_of_le hle
    let f : OE → Module.End C W := fun a => (ρ a).restrict (hW a)
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => LinearMap.restrict_commute (hcomm a b) (hW a) (hW b))
      (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
    have hv : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
    have hle : (⊤ : Submodule C W) ≤ Submodule.comap W.subtype
        (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) := by
      rw [← htop]
      refine iSup_le fun χ x hx => ?_
      refine mem_iSup_of_eigenvector C OE V ρ χ x fun a => ?_
      have h1 := (Submodule.mem_iInf _).mp hx a
      have h2 : (f a).IsSemisimple := (hss a).restrict (hW a)
      rw [h2.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
        Module.End.mem_eigenspace_iff] at h1
      exact congrArg Subtype.val h1
    exact hle (Submodule.mem_top (x := (⟨v, hv⟩ : W)))

end GlobalTheory
end

