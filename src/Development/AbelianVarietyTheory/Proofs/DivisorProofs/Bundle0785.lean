import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FloorCastOfInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes
open Formalism.MainNotions.DIV.Inh (aPlusQ_anti aMinusQ_mono)

namespace GlobalTheory.BlockRows

theorem floor_cast_of_int {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem one_le_aPlusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : 1 ≤ DV.aPlusQ D j τ i := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  exact (DV.aPlusQ_last D j h1 h2 τ).trans
    (aPlusQ_anti D j τ (show i.1 ≤ D.R.k + j - 1 - 1 by omega) (by omega))

theorem one_le_aMinusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c < D.R.m) :
    1 ≤ DV.aMinusQ D j τ c :=
  (DV.aMinusQ_last D j h1 (by omega) τ).trans (aMinusQ_mono D j τ (Nat.zero_le c) hc)

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem aPlus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (i : Fin (D.R.sigW j).1) : DV.aPlus D j τ i ≤ 3 * L.sc.b ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  have h0 : 0 < D.R.k - 1 := by omega
  have a1 := aPlusQ_anti D j τ (Nat.zero_le i.1) (by omega)
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aPlusQ D j τ 0 ≤ (D.hc τ).v ⟨0, h0⟩ + (D.hc τ).e ⟨j - 1, hj⟩ := by
    rw [DV.aPlusQ_eq]
    unfold DV.sigPar DV.eQ
    rw [dif_pos h0, dif_pos ⟨h1, h2⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hk' : (2 : ℚ) ≤ D.R.k := by exact_mod_cast (show 2 ≤ D.R.k by omega)
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith
  have a3 : DV.aPlus D j τ i ≤ (((D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aPlus
    exact_mod_cast a1.trans a2
  have b1 := (L.cloud_v τ ⟨0, h0⟩).2
  have b2 := L.b_le τ ⟨j - 1, hj⟩
  have b3 := (abs_le.1 (L.be_close τ ⟨j - 1, hj⟩ ⟨j - 1, hj⟩)).1
  have b4 := one_le_b L.sc
  push_cast at b3
  have := hL.1
  have := hL.2
  nlinarith

theorem aMinus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (c : ℕ) (hc : j + c < D.R.m) : DV.aMinus D j τ c ≤ 3 * L.sc.b ^ 2 := by
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aMinusQ D j τ c ≤ (D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ := by
    unfold DV.aMinusQ DV.eQ
    rw [dif_pos hc, dif_pos ⟨h1, by omega⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hc' : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    linarith
  have a3 : DV.aMinus D j τ c ≤ (((D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aMinus
    exact_mod_cast a2
  have b3 := (abs_le.1 (L.be_close τ ⟨j + c, hc⟩ ⟨j - 1, hj⟩)).2
  have b4 := one_le_b L.sc
  have := hL.1
  nlinarith

theorem rows_sizes : ∀ (D : D7) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, (Antitone (rowsP D j τ) ∧ (∀ i, 1 ≤ rowsP D j τ i) ∧ ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i) ∧ (Antitone (rowsM D j τ) ∧ (∀ i, 1 ≤ rowsM D j τ i) ∧ ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)) ∧ ∀ L : SizeData₂ D, WindowsLe L → (∀ i, (rowsP D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2) ∧ ∀ i, (rowsM D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2 := by
  intro D j h1 h2 τ
  have hk := D.R.m_add_three_le_k
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hM : ∀ i : Fin (D.R.sigW j).2, j + ((D.R.sigW j).2 - 1 - i) < D.R.m := by
    intro i
    have := i.2
    omega
  have eP : ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i := by
    intro i
    have := floor_cast_of_int (DV.aPlusQ_int D j τ i) (one_le_aPlusQ D j h1 h2 τ i)
    unfold DV.aPlus rowsP
    rw [← this]
    simp
  have eM : ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i) := by
    intro i
    have := floor_cast_of_int (DV.aMinusQ_int D j τ _) (one_le_aMinusQ D j h1 τ _ (hM i))
    unfold DV.aMinus rowsM
    rw [← this]
    simp
  refine ⟨⟨?_, ?_, eP⟩, ⟨?_, ?_, eM⟩, fun L hL => ⟨fun i => ?_, fun i => ?_⟩⟩
  · intro a b hab
    have hb : b.1 < D.R.k + j - 1 := b.2
    exact Nat.floor_le_floor (aPlusQ_anti D j τ (show a.1 ≤ b.1 from hab) (by omega))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aPlusQ D j h1 h2 τ i)
  · intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    exact Nat.floor_le_floor (aMinusQ_mono D j τ (by omega) (hM a))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aMinusQ D j h1 τ _ (hM i))
  · rw [eP]
    exact aPlus_le D j h1 h2 τ L hL i
  · rw [eM]
    exact aMinus_le D j h1 τ L hL _ (hM i)

end GlobalTheory.BlockRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfParts
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem taylor_congr {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    {f f' : (I → ℂ) → ℂ} (h : f =ᶠ[nhds 0] f') : taylor N t f = taylor N t f' := by
  unfold taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem isAb_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h

theorem gaussManinPeriods_of_parts : ∀ ε : ℤˣ, GlobalTheory.PeriodFamily.FamUnif → PExist → PHom → PSpan → PLie → PEnd → PChern ε → PFix → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  intro ε HF HE HH HS HL HEn HC HX HT
  have pm : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (L : LB A.left), L.IsLB → ∀ (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P → IsPeriodMap ε u P :=
    fun A _ g hA hg L hL u P hP ↦ ⟨(HS A g hA hg L u P hP).1, (HS A g hA hg L u P hP).2, HL A g hA hg L u P hP,
      fun α _ M ↦ HEn A g hA L u P hP α M, fun H χ ψ ↦ HC A g hA L u P hP L u hL rfl H χ ψ⟩
  refine ⟨ε, fun B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0 hy A _ φ hφ m L hL A₀ _ φ₀ hφ₀ L₀ hL₀ u₀ ↦ ?_⟩
  obtain ⟨r, u, τ, hr, hrU, hhol, ⟨W, hW, hW0⟩, c1, c2, c3, c4⟩ :=
    HF B 𝒜 g h𝒜 hg I U y hU h0 hy A φ hφ L hL A₀ φ₀ hφ₀ L₀ u₀
  have hA : ∀ z, IsAbelianScheme (A z) := fun z ↦ isAb_pull (hφ z) h𝒜
  have hA₀ : IsAbelianScheme A₀ := isAb_pull hφ₀ h𝒜
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have gA : ∀ z, SmoothOfRelativeDimension g (A z).hom := fun z ↦
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (hφ z).1 hg
  have gA₀ : SmoothOfRelativeDimension g A₀.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hφ₀.1 hg
  choose P hP using fun z ↦ HH (A z) g (hA z) (L z) (u z)
  obtain ⟨P₀, hP₀⟩ := HH A₀ g hA₀ L₀ u₀
  let V : Opens (I → ℂ) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have V0 : (0 : I → ℂ) ∈ V := Metric.mem_ball_self hr
  let F : Fam I g u₀.Λ :=
    { V := V
      τ := { toFun x z := (τ z x : Fin g → ℂ)
             map_zero' := funext fun z ↦ by simp
             map_add' a b := funext fun z ↦ by simp }
      hol x := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (c3 x) }
  have ya : ∀ b, AnalyticOnNhd ℂ (fun z ↦ y z b) V := fun b ↦
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball ((hy b).mono hrU)
  let σ : B →ₐ[ℂ] Hol F.V :=
    { toFun b := Hol.mk _ (ya b)
      map_one' := Subtype.ext (funext fun z ↦ map_one (y z))
      map_mul' a b := Subtype.ext (funext fun z ↦ map_mul (y z) a b)
      map_zero' := Subtype.ext (funext fun z ↦ map_zero (y z))
      map_add' a b := Subtype.ext (funext fun z ↦ map_add (y z) a b)
      commutes' a := Subtype.ext (funext fun z ↦ (y z).commutes a) }
  have hσ : ∀ b, ∀ z ∈ V, (σ b).fn z = y z b := fun b z hz ↦ Hol.fn_mk _ (ya b) hz
  let e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V) :=
    { E q := (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1
      w p hp := by
        have e1 : (show Sp ℂ ⟶ (A p.1).left from ((u p.1).ex p.2).left) ≫ (A p.1).hom = 𝟙 _ := Over.w ((u p.1).ex p.2)
        rw [Category.comp_id, Category.assoc, (hφ p.1).1.w, ← Category.assoc, e1, Category.id_comp]
        rfl
      per l p _ := by
        have : (u p.1).ex (p.2 + (τ p.1 l : Fin g → ℂ)) = (u p.1).ex p.2 := by
          rw [(u p.1).ex_add, ((u p.1).ker _).2 (τ p.1 l).2, _root_.mul_one]
        exact congrArg (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A p.1 ↦ (show Sp ℂ ⟶ (A p.1).left from x.left) ≫ φ p.1) this
      hol U' f := by
        have := hhol U' f
        simp only [Set.mem_prod, Set.mem_univ, and_true] at this
        exact this }
  haveI : IsSeparated (𝒜.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]
    haveI := h𝒜.proper
    infer_instance
  choose per hper using HE I g u₀.Λ F B 𝒜.left _ _ e ⟨W, hW, hW0⟩
  have fix : ∀ x (c : primDR 𝒜), ∀ z ∈ V, P z (τ z x) ((m z).pull c) = (per c.1 x).fn z := fun x c z hz ↦
    HX I g u₀.Λ F B 𝒜 h𝒜 _ e z hz _ (fun b ↦ (hσ b z hz).symm) (A z) (hA z) (φ z) (m z) (L z) (u z) (fun _ ↦ rfl)
      (τ z).toAddMonoidHom (fun _ ↦ rfl) (P z) (hP z) c _ (hper c.1) x
  have nV : (V : Set (I → ℂ)) ∈ nhds (0 : I → ℂ) := V.isOpen.mem_nhds V0
  refine ⟨Metric.ball 0 r, u, τ, P, P₀, Metric.isOpen_ball, V0, hrU, pm A₀ g hA₀ gA₀ L₀ hL₀ u₀ P₀ hP₀,
    fun z _ ↦ pm _ g (hA z) (gA z) _ (hL z) _ _ (hP z), c1, c2, c3, c4,
    fun x c ↦ (per c.1 x).analytic.differentiableOn.congr (fix x c), ?_⟩
  intro D _ _ π κ hκ hπ N t ht hN j hj A' _ φ' hφ' m' i h hi k x d hd c
  rw [HT I g B 𝒜 h𝒜 hg (y 0) A₀ φ₀ hφ₀ L₀ u₀ F σ e V0 (fun b ↦ (hσ b 0 V0).symm) c1 (fun x ↦ c2 x) P₀ hP₀ D π κ hκ hπ N t ht hN j
    (fun b ↦ (hj b).trans (taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (hσ b z hz).symm)))
    A' φ' hφ' m' i h hi k x d hd c _ (hper c.1)]
  exact taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (fix x c z hz).symm)

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  first | exact @GlobalTheory.CechPer.isPer_of_basis | exact GlobalTheory.CechPer.isPer_of_basis | (intros; apply GlobalTheory.CechPer.isPer_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  first | exact @GlobalTheory.CechPer.zero_periods_eq_zero | exact GlobalTheory.CechPer.zero_periods_eq_zero | (intros; apply GlobalTheory.CechPer.zero_periods_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFinGLLeInvAbsDet
section
open NumberField IsDedekindDomain GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af finGL)

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finGL_apply (k : GL (Fin n) (Af K)) (a b : Fin n) :
    ((finGL K n k : GA K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b =
      (1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b
        - GlobalTheory.CuspRep.sFin K ((1 : Matrix (Fin n) (Fin n) (Af K)) a b)
        + GlobalTheory.CuspRep.sFin K ((k : Matrix (Fin n) (Fin n) (Af K)) a b) := rfl

theorem sFin_fst (x : Af K) : (GlobalTheory.CuspRep.sFin K x).1 = 0 := rfl

end GlobalTheory.HenQ

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end GlobalTheory.HenQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphismStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  first | exact @GlobalTheory.AnPer.isPeriod_pull1_eq_comap | exact GlobalTheory.AnPer.isPeriod_pull1_eq_comap | (intros; apply GlobalTheory.AnPer.isPeriod_pull1_eq_comap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleModuleInfId
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ.DetSplit

variable {K : Type} [Field K] [NumberField K] [IsTotallyReal K] {n : ℕ}

omit [NumberField K] in
theorem norm_realSymm (w : InfinitePlace K) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

theorem ideleModule_infId (u : (Rinf K)ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (UpperTheory.V.TR.infId K u) : ℝ) = ∏ w, |u.val w| := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val := by
    show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1 := by
    show (1 : Af K) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_realSymm w (u.val w)

end GlobalTheory.HenQ.DetSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open GlobalTheory.Published.StrongApprox
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormFin

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  by
  apply RestrictedProduct.ext
  intro w
  exact h w

def iotaL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by change (0 : Ainf F) = 0 + 0; simp) ?_
    change singleV F v (a + b) = singleV F v a + singleV F v b
    refine af_ext fun w => ?_
    rw [map_add]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, add_zero]
  map_smul' c a := by
    refine Prod.ext (by change (0 : Ainf F) = c • 0; simp) ?_
    change singleV F v (c • a) = c • singleV F v a
    refine af_ext fun w => ?_
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, smul_zero]

theorem iotaL_apply (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    iotaL v a = pairA F 0 (singleV F v a) := rfl

theorem iotaL_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    iotaL v (a * b) = iotaL v a * iotaL v b := by
  refine Prod.ext (by change (0 : Ainf F) = 0 * 0; simp) ?_
  change singleV F v (a * b) = singleV F v a * singleV F v b
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; simp only [evalV_single_same]
  · simp only [evalV_single_ne hw, mul_zero]

theorem idem_mul_iotaL (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (a : Fv F v) :
    ε * iotaL v a = iotaL v a := by
  refine Prod.ext (by change fstA F ε * 0 = 0; simp) ?_
  change sndA F ε * singleV F v a = singleV F v a
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [hε.2.2.1 w (Finset.mem_singleton_self w), one_mul]
  · simp only [evalV_single_ne hw, mul_zero]

theorem iotaL_one (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) :
    iotaL v 1 = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    exact (hε.2.1 w (Finset.notMem_empty w)).symm
  · change singleV F v 1 = sndA F ε
    refine af_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same, hε.2.2.1 w (Finset.mem_singleton_self w)]
    · rw [evalV_single_ne hw, hε.2.2.2 w (fun h => hw (Finset.mem_singleton.1 h))]

section Tensor

variable {E : Type} [Field E] [Algebra F E]

def phi (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (iotaL v) LinearMap.id

theorem phi_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    phi v (a ⊗ₜ[F] e) = iotaL v a ⊗ₜ[F] e := TensorProduct.map_tmul _ _ _ _

theorem phi_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v ⊗[F] E) :
    phi v (x * y) = phi v x * phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, phi_tmul, phi_tmul, phi_tmul, iotaL_mul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]

theorem phi_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    phi v (sigR (Fv F v) σ x) = sigR (AF F) σ (phi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, phi_tmul]
  | add x z hx hz => rw [map_add, map_add, hx, hz, map_add, map_add]

theorem idem_mul_phi (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε)
    (x : Fv F v ⊗[F] E) : algebraMap (AF F) (AF F ⊗[F] E) ε * phi v x = phi v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, idem_mul_iotaL v ε hε]
  | add x z hx hz => rw [map_add, mul_add, hx, hz]

theorem phi_inclR (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (c : E) :
    phi v (inclR (Fv F v) c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  change phi v ((1 : Fv F v) ⊗ₜ[F] c) = algebraMap (AF F) (AF F ⊗[F] E) ε * ((1 : AF F) ⊗ₜ[F] c)
  rw [phi_tmul, iotaL_one v ε hε, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Tensor

theorem idem_norm_eq_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E,
    (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ v ε hε c ⟨t, ht⟩
  refine ⟨phi v t, ?_⟩
  rw [← phi_sig, ← phi_mul, mul_add, idem_mul_phi v ε hε, ← phi_inclR v ε hε, ← map_add, ht, map_zero]

end GlobalTheory.NormFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideAlt
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgTau

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ IsAlgebraic ℚ (jT τ) ∧ IsAlgebraic ℚ (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) ∧ ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), IsAlgebraic ℚ (wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro K _ _ d δ ι 𝔞 Λ c Ω τ hd hδ hlat htau hΩ
  obtain ⟨-, hmul, him, -⟩ := GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier K d δ ι 𝔞 Λ hd hδ hlat
  have hval := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ htau
  have halg := GlobalTheory.T.algebraic_normalized_weierstrass_values_cm Λ (ι δ) Ω hmul him hΩ
  refine ⟨(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD Λ c τ htau).2 Ω hΩ, ?_, ?_, ?_⟩
  · have hj : IsIntegral ℤ (jT τ) := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ (ι δ) htau hmul him
    exact (hj.tower_top (A := ℚ)).isAlgebraic
  · rw [hval.1]; exact halg.1
  · intro N _ x
    rw [(hval.2 N x).1]
    have hN : (N : ℂ) * (c * tors N τ x) ∈ Λ.lattice := by
      have h1 := ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ htau).1 ((N : ℂ) * tors N τ x)).2
        ((GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ).2.2.2.1 x)
      simpa [mul_left_comm] using h1
    exact (halg.2 N (c * tors N τ x) (Nat.pos_of_ne_zero (NeZero.ne N)) hN).1

end GlobalTheory.AlgTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  first | exact @GlobalTheory.LieLin.main | exact GlobalTheory.LieLin.main | (intros; apply GlobalTheory.LieLin.main <;> assumption)
end

