import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartNsmulAndKilledByPPowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianFunctorNilChart_nsmul_and_killed_by_p_pow : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by
  first | exact @GlobalTheory.ChF.bxChart_nsmul_and_killed | exact GlobalTheory.ChF.bxChart_nsmul_and_killed | (intros; apply GlobalTheory.ChF.bxChart_nsmul_and_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  first | exact @GlobalTheory.ChF.bxChart_of_nilChart | exact GlobalTheory.ChF.bxChart_of_nilChart | (intros; apply GlobalTheory.ChF.bxChart_of_nilChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMem
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CvDiv

variable {C : Type} [Field C]

theorem coeff_alongCv_le {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ}
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, mul_zero, Finset.sum_const_zero]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 hf
  · exact coeff_alongCv_low hn hγ hf

theorem coeff_alongCv_smul {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (c : C)
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv (c • γ) f) = c * PowerSeries.coeff n (alongCv γ f) := by
  rw [coeff_alongCv_le h0 hγ hf, coeff_alongCv_le (fun i => by simp [h0 i])
    (fun i m hm => by simp [hγ i m hm]) hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem isCv_smul {V : VF C} {σ : Type} {γ : σ → PowerSeries C} {c : C} (hc : V.Ge 0 c)
    (h : IsCv V γ) : IsCv V (c • γ) := fun i =>
  ⟨by simp [(h i).1], fun n => by
    simpa only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul] using hc.mul_int ((h i).2 n)⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem step {X : RawChart C d I κ} {V : VF C} (hX : RLaw X V) (g : Fin 2) {c : C} (hc : V.Ge 0 c)
    (m : ℕ) {a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)} (ha : a ∈ Cv X V g)
    (hv : ∀ i, ∀ k < m, PowerSeries.coeff k (a.1 i) = 0) :
    ∃ b ∈ Cv X V g, ∀ k ≤ m, (∀ i, PowerSeries.coeff k (b.1 i) = c * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (b.2 q) = c * PowerSeries.coeff k (a.2 q) := by
  classical
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hX.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hord : ∀ k, k < m → ∀ i, PowerSeries.coeff k (γ i) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i
      have e1 := coeff_alongCv_le h0 (fun i m' hm' => ih m' hm' (by omega) i) (hlg0 i)
      rw [h1 i, hv i k hk] at e1
      simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1
      exact e1.symm
  refine ⟨(fun i => alongCv (c • γ) (X.lg i), fun q => (c • lam) q - alongCv (c • γ) (X.sg (X.u (1 - g) q))),
    ⟨c • γ, c • lam, isCv_smul hc hγ, isCv_smul hc hlam, fun _ => rfl, fun _ => rfl⟩, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [← h1 i]
    exact coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (hlg0 i)
  · rw [h2 q]
    simp only [map_sub, Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
    rw [coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (X.constantCoeff_sg (hX.axes 0) _)]
    ring

end GlobalTheory.RowLaw.CvDiv

namespace GlobalTheory.RowLaw

open CvDiv in

theorem cv_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g N hN a ha
  obtain ⟨hzero, hadd, hneg, -⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  have hN0 : (N : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hN
    exact WithTop.top_ne_zero hN
  have hc : V.Ge 0 (N : C)⁻¹ := by
    have h := V.v.map_mul (N : C) (N : C)⁻¹
    rw [mul_inv_cancel₀ hN0, V.v.map_one, hN, zero_add] at h
    unfold VF.Ge
    rw [← h]
    exact le_rfl
  have hns : ∀ s ∈ Cv X V g, ∀ n : ℕ, (n : C) • s ∈ Cv X V g := by
    intro s hs n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul]
      exact hadd _ ih _ hs
  have key : ∀ m : ℕ, ∃ s ∈ Cv X V g, ∀ k < m,
      (∀ i, PowerSeries.coeff k (s.1 i) = (N : C)⁻¹ * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (s.2 q) = (N : C)⁻¹ * PowerSeries.coeff k (a.2 q) := by
    intro m
    induction m with
    | zero => exact ⟨0, hzero, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨s, hs, hsa⟩ := ih
      have hr : a + -((N : C) • s) ∈ Cv X V g := hadd _ ha _ (hneg _ (hns s hs N))
      obtain ⟨b, hb, hba⟩ := step hX g hc m hr (fun i k hk => by
        simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hsa k hk).1 i]
        field_simp
        ring)
      refine ⟨s + b, hadd _ hs _ hb, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
      · simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).1 i]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).2 q]
        field_simp
        ring
  choose s hs hsa using key
  refine GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits C V d I κ X hX g s _ hs fun m => ⟨m + 1, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [(hsa n m (by omega)).1 i]
    simp
  · rw [(hsa n m (by omega)).2 q]
    simp

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplitStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_hEnd_sub_hEnd_mem_logInt : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  first | exact @GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | exact GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | (intros; apply GlobalTheory.RowVal.MapSumDiagonal.diagonal_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualNumberPointPreimageTopOfReduction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma dualNumberPoint_preimage_top_of_reduction {O : Type} [CommRing O] {d r g m : ℕ} (A : Matrix (Fin d) (Fin r) O)
    (B : Matrix (Fin g) (Fin d) O) (h : SplitEx A B) (s : Fin m → Fin d → O)
    (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1) (f : Fin d → O) :
    ∃ (t : Fin d → O) (l : Fin g → O), t ∈ Submodule.span O (Set.range s) ∧ f = t + Bᵀ *ᵥ l := by
  obtain ⟨-, A', B', -, -, h3⟩ := h
  choose k hk using hT
  set t : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with ht
  have h0 : Aᵀ *ᵥ (f - t) = 0 := by
    rw [Matrix.mulVec_sub, ht, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    rw [sub_eq_zero]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (A * A' + B' * B)ᵀ *ᵥ (f - t) = f - t := by rw [h3]; simp
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add] at h1
  refine ⟨t, B'ᵀ *ᵥ (f - t), ?_, by rw [h1]; abel⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)

private lemma idem_fix {O E : Type} [CommRing O] {g m : ℕ} (ρ : E → Matrix (Fin g) (Fin g) O)
    (ε : Fin m → Matrix (Fin g) (Fin g) O) (sg : Fin m → E → O)
    (horth : ∀ i j, ε i * ε j = if i = j then ε i else 0) (hsum : ∑ i, ε i = 1)
    (heig : ∀ a i, ρ a * ε i = sg i a • ε i) (i : Fin m)
    (hd : ∀ j, i ≠ j → ∃ a, IsUnit (sg i a - sg j a)) (y : Fin g → O)
    (hy : ∀ a, ρ a *ᵥ y = sg i a • y) : ε i *ᵥ y = y := by
  have hl : ∀ a j, ε j * ρ a = sg j a • ε j := by
    intro a j
    have : ρ a = ∑ k, sg k a • ε k := by
      rw [← Matrix.mul_one (ρ a), ← hsum, Matrix.mul_sum]
      simp only [heig]
    rw [this, Matrix.mul_sum]
    simp only [Matrix.mul_smul, horth]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hz : ∀ j, i ≠ j → ε j *ᵥ y = 0 := by
    intro j hj
    obtain ⟨a, ha⟩ := hd j hj
    have h1 : ε j *ᵥ (ρ a *ᵥ y) = sg j a • (ε j *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec]
    rw [hy, Matrix.mulVec_smul] at h1
    have h2 : (sg i a - sg j a) • (ε j *ᵥ y) = 0 := by rw [sub_smul, h1, sub_self]
    exact (ha.smul_eq_zero).1 h2
  have h3 : (∑ j, ε j) *ᵥ y = y := by rw [hsum]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h3
  · exact h3
  · intro b _ hb
    exact hz b hb.symm
  · simp

theorem cokE_surj_res_quot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (i : Fin U.m) (τ : OE →+* O), (∀ x, U.sg i x = tauExt τ x) → ∀ (n : ℕ) (W : Fin n → Fin d → O), EigB ρG τ W → ∃ f : cokE H.Ht U.εT U.εL i (U.cj i) →ₗ[O] ((Fin n → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k))), Function.Surjective f := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp _ g H d r m A B ρG N s hL U i τ hτ n W hW
  have hsurj := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d n ρG τ W hW).1
  have hZ : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] (1 : OE)) = algebraMap ℤ_[p] O c • 1 := fun c =>
    (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g (H.ρL.comp Algebra.TensorProduct.includeLeftRingHom) c
  have hy : ∀ l x, H.ρL x *ᵥ (B *ᵥ W l) = U.sg i x • (B *ᵥ W l) := by
    intro l x
    rw [hτ]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, Matrix.add_mulVec, hx, hy, add_smul]
    | tmul c a =>
      have e : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : tauExt τ (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [e2, e, map_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
        ← hL.eqB, ← Matrix.mulVec_mulVec, hW.1, Matrix.mulVec_smul, mul_smul]
  have hfix : ∀ l, U.εL i *ᵥ (B *ᵥ W l) = B *ᵥ W l := fun l =>
    idem_fix (fun x => H.ρL x) U.εL (fun j x => U.sg j x) U.εL_orth U.εL_sum U.εL_eig i
      (fun j hj => by
        obtain ⟨a, ha⟩ := U.distinct i j hj
        exact ⟨a, hv.isUnit_of_one' ha⟩) _ (hy l)
  have hres : ∀ l : Fin g → O, Pdiv.ChartF.res W (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = Pdiv.ChartF.res W (Bᵀ *ᵥ l) := by
    intro l
    ext k
    change W k ⬝ᵥ (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = W k ⬝ᵥ (Bᵀ *ᵥ l)
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hfix, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  set S : Submodule O (Fin n → O) := Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k)) with hS
  have hSm : ∀ t ∈ Submodule.span O (Set.range s), Pdiv.ChartF.res W t ∈ S := by
    intro t ht
    have := Submodule.mem_map_of_mem (f := Pdiv.ChartF.res W) ht
    rwa [Submodule.map_span, ← Set.range_comp] at this
  let F : LinearMap.range (Matrix.mulVecLin (U.εL i)ᵀ) →ₗ[O] ((Fin n → O) ⧸ S) :=
    S.mkQ ∘ₗ Pdiv.ChartF.res W ∘ₗ Matrix.mulVecLin Bᵀ ∘ₗ Submodule.subtype _
  have hF : ∀ x, F x = S.mkQ (Pdiv.ChartF.res W (Bᵀ *ᵥ x.1)) := fun x => rfl
  refine ⟨Submodule.liftQ _ F ?_, ?_⟩
  · rintro x ⟨ν, -, hx⟩
    rw [LinearMap.mem_ker, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply hSm
    have hx' : x.1 = ∑ c, ν c • (fun l => H.Ht l c) := by
      have : H.Ht *ᵥ ν = x.1 := hx
      rw [← this]
      ext l
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hx', Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨k, hk⟩ := hL.fromB c
    rw [Matrix.mulVec_smul, ← hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro z
    obtain ⟨z, rfl⟩ := S.mkQ_surjective z
    obtain ⟨f, rfl⟩ := hsurj z
    obtain ⟨t, l, ht, rfl⟩ := dualNumberPoint_preimage_top_of_reduction A B hL.exact s hL.fromT f
    refine ⟨Submodule.Quotient.mk ⟨(U.εL i)ᵀ *ᵥ l, l, rfl⟩, ?_⟩
    rw [Submodule.liftQ_apply, hF, hres, map_add, map_add]
    have : S.mkQ (Pdiv.ChartF.res W t) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (hSm t ht)
    rw [this, zero_add]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariantStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_restriction_surjective_equivariant : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  first | exact @GlobalTheory.ChF.eigB_res_surjective | exact GlobalTheory.ChF.eigB_res_surjective | (intros; apply GlobalTheory.ChF.eigB_res_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigAdd

private theorem trace_eq (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)]
    (V : Type) [AddCommGroup V] [Module C V] [Module.Finite C V] (ρ : OE →+* Module.End C V) (a : OE) :
    LinearMap.trace C V (ρ a) = ∑ τ : OE →+* C,
      (Module.finrank C ↥(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) : C) * τ a := by
  classical
  obtain ⟨h1, h2⟩ := (GlobalTheory.order_rep_diagonalisable C OE).2 V ρ
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h1 h2
  have hv : ∀ (τ : OE →+* C) (v : V), v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) → ρ a v = τ a • v :=
    fun τ v hv => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  have hf : ∀ τ : OE →+* C, Set.MapsTo (ρ a) ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b))
      ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := fun τ v h => by
    have h' : v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := h
    have := Submodule.smul_mem _ (τ a) h'
    rw [← hv τ v h'] at this
    exact this
  rw [LinearMap.trace_eq_sum_trace_restrict hI hf]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : (ρ a).restrict (hf τ) = τ a • LinearMap.id := by
    ext v
    exact hv τ v.1 v.2
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

private theorem trace_mat (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)] (d : ℕ)
    (ρ : OE →+* Matrix (Fin d) (Fin d) O) (a : OE) :
    algebraMap O C (ρ a).trace = ∑ τ : OE →+* C, (eigDim C ρ τ : C) * τ a := by
  have := trace_eq C OE (Fin d → C)
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin d)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)) a
  refine Eq.trans ?_ this
  change _ = LinearMap.trace C _ (Matrix.toLin' ((ρ a).map (algebraMap O C)))
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]

private theorem coeff_eq (C : Type) [Field C] [CharZero C] (OE : Type) [CommRing OE] [Fintype (OE →+* C)]
    (m n : (OE →+* C) → ℕ) (h : ∀ a, ∑ τ : OE →+* C, (m τ : C) * τ a = ∑ τ : OE →+* C, (n τ : C) * τ a)
    (τ : OE →+* C) : m τ = n τ := by
  have li : LinearIndependent C (fun τ : OE →+* C => (τ : OE → C)) :=
    (linearIndependent_monoidHom OE C).comp (fun τ : OE →+* C => (τ : OE →* C))
      RingHom.coe_monoidHom_injective
  have := Fintype.linearIndependent_iffₛ.1 li (fun τ => (m τ : C)) (fun τ => (n τ : C))
    (by funext a; simpa [Finset.sum_apply] using h a) τ
  exact_mod_cast this

private def trHom {O OE : Type} [CommRing O] [CommRing OE] {d : ℕ} (ρ : OE →+* Matrix (Fin d) (Fin d) O) :
    OE →+* Matrix (Fin d) (Fin d) O where
  toFun a := (ρ a)ᵀ
  map_one' := by simp
  map_mul' a b := by rw [mul_comm a b, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp

theorem eigDim_add_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  intro C _ _ _ O _ _ OE _ _ _ _ _ d r g A B hS ρ ρA ρB hB hA τ
  haveI : Finite (OE →+* C) := (GlobalTheory.order_rep_diagonalisable C OE).1
  letI : Fintype (OE →+* C) := Fintype.ofFinite _
  obtain ⟨-, A', B', h1, h2, h3⟩ := hS
  constructor
  · refine coeff_eq C OE (fun τ => eigDim C ρ τ) (fun τ => eigDim C ρA τ + eigDim C ρB τ) (fun a => ?_) τ
    have ht : (ρ a).trace = (ρA a).trace + (ρB a).trace := by
      have e1 : (ρ a * (A * A')).trace = (ρA a).trace := by
        rw [← Matrix.mul_assoc, hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have e2 : (ρ a * (B' * B)).trace = (ρB a).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, h2,
          Matrix.mul_one]
      rw [← e1, ← e2, ← Matrix.trace_add, ← Matrix.mul_add, h3, Matrix.mul_one]
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← trace_mat, ← trace_mat, ← trace_mat, ht, map_add]
  · refine coeff_eq C OE (fun τ => eigDim C (trHom ρ) τ) (fun τ => eigDim C ρ τ) (fun a => ?_) τ
    rw [← trace_mat, ← trace_mat]
    exact congrArg _ (Matrix.trace_transpose _)

end GlobalTheory.EigAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddings_lift_integers_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  first | exact @GlobalTheory.ChF.embeddings_idempotents_conjugation | exact GlobalTheory.ChF.embeddings_idempotents_conjugation | (intros; apply GlobalTheory.ChF.embeddings_idempotents_conjugation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPartStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEnd_of_action_linearPart : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  first | exact @GlobalTheory.ActionEnd.exists_isEnd_act | exact GlobalTheory.ActionEnd.exists_isEnd_act | (intros; apply GlobalTheory.ActionEnd.exists_isEnd_act <;> assumption)
end

