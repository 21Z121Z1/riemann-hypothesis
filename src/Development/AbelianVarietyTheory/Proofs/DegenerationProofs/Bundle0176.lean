import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0174

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcSeries

theorem exists_root_system {K : Type} [Field K] [IsAlgClosed K] (u : Kˣ) : ∃ r, Roots u r := by
  have hs : ∀ (n : ℕ) (x : Kˣ), ∃ y : Kˣ, y ^ (n + 1) = x := fun n x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) n.succ_pos
    exact ⟨Units.mk0 y fun e => x.ne_zero (by rw [← hy, e]; simp), Units.ext hy⟩
  choose rt hrt using hs
  let s : ℕ → Kˣ := fun n => Nat.rec u (fun n x => rt n x) n
  have h1 : ∀ n d, s (n + d) ^ ((n + d).factorial / n.factorial) = s n := fun n d => by
    induction d with
    | zero => simp [Nat.div_self n.factorial_pos]
    | succ d ih =>
      rw [← add_assoc, Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)),
        pow_mul]
      exact (congrArg (· ^ _) (hrt _ _)).trans ih
  refine ⟨fun n => s n ^ (n.factorial / n), ?_, fun n m hn hm => ?_⟩
  · change s 1 ^ 1 = u
    exact hrt 0 u
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_right n hm)
    have a := h1 n d
    rw [← hd] at a
    change (s (n * m) ^ ((n * m).factorial / (n * m))) ^ m = s n ^ (n.factorial / n)
    rw [← a, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨p, hp⟩ := Nat.dvd_factorial (Nat.mul_pos hn hm) le_rfl
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hn le_rfl
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)
    have e1 : (n * m).factorial / (n * m) = p := by rw [hp]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos hn hm)
    have e2 : n.factorial / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
    have e3 : (n * m).factorial / n.factorial = t := by rw [ht]; exact Nat.mul_div_cancel_left _ n.factorial_pos
    rw [e1, e2, e3]
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [hp, hq] at ht
    linarith

theorem base_local {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    IsLocalRing O ∧ IsPrincipalIdealRing O := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_reps {n : ℕ} (hn : 0 < n) : ∃ (Ix : Type) (_ : Finite Ix) (t : Ix → D.La), ∀ a, ∃ i e, t i = a + n • e := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let P : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • LinearMap.id)
  have : Finite (D.La ⧸ P) := Module.finite_of_fg_torsion (M := D.La ⧸ P) fun x => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero P).2 ⟨x, rfl⟩
  refine ⟨D.La ⧸ P, this, Quotient.out, fun a => ?_⟩
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq P).1 (Quotient.out_eq (Submodule.Quotient.mk a : D.La ⧸ P))
  exact ⟨_, e, by rw [← natCast_zsmul]; exact (eq_add_of_sub_eq' he.symm)⟩

theorem eq_zero_of_nsmul {n : ℕ} (hn : n ≠ 0) (a : D.La) (h : n • a = 0) : a = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun x => D.EF x y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hn, false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

theorem exists_series : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → Nonempty (Ser a K (algebraMap _ K)) := by
  intro hHV _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB K _ _ _ _ _ _ hK
  have hL : Laws := hHV.1.1
  have hL2 : Laws2 := hHV.1.2.1
  have gt := GlobalTheory.T.torus_torsion_points_correspond_values
  have wp := GlobalTheory.T.torsionPairing_values_of_familiesValues gt (GlobalTheory.T.families_values_correspond hL hL2)
  obtain ⟨_, _⟩ := base_local hB
  let F := AlgebraicClosure (FractionRing O')
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR O' ϖ hB F
  have hin : ∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S₀ := fun r =>
    (hS₀ _).2 (by rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap)
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.exists_arcIsometry_torsion_integralGauge hL gt E H D l Xo c W₀ Y O' b ϖ a hB F S₀ hin
  let io : F →+* K := (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).toRingHom
  have hio : io.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') K :=
    (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).comp_algebraMap
  obtain ⟨A, -, I₀, l₀, -, -, x₀, q₀⟩ :=
    GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB F K io hio ⊤ (fun _ => trivial) A₀
  have hinj := FaithfulSMul.algebraMap_injective (PowerSeries O') K
  have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  obtain ⟨r, hr⟩ := exists_root_system (Units.mk0 _ hX)
  have hr1 : (r 1 : K) = algebraMap (PowerSeries O') K PowerSeries.X := by rw [hr.1]; rfl
  obtain ⟨iθ, iσ, ith, iψ⟩ := GlobalTheory.T.integralGauge_values_are_valuationUnits O' a.D₀ F S₀ hin A₀.N A₀.ν hA₀
  have level : ∀ (m j : ℕ) (z : D.La), ∃ (R₁ : Subalgebra (PowerSeries O') K) (v w : D.La → K), Odd m → 0 < j →
      Module.Finite (PowerSeries O') R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O') io A₀.N A₀.be.be m j (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j)) v w := by
    intro m j z
    by_cases h : Odd m ∧ 0 < j
    swap
    · exact ⟨⊥, 0, 0, fun a b => (h ⟨a, b⟩).elim⟩
    obtain ⟨hm, hj⟩ := h
    have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
    obtain ⟨Ix, _, t, ht⟩ := exists_reps D hm2
    let k : Option Ix → ℕ := fun i => i.elim j fun _ => m ^ 2
    let p : ∀ i, A₀.N.QT (k i) := fun i => match i with
      | none => A₀.q j z
      | some i => A₀.q (m ^ 2) (t i)
    obtain ⟨K₁, A₁, f1, f2, f3, f4, f5, f6, f7⟩ :=
      GlobalTheory.T.exists_finiteDimensional_field_degenerationValues O' a.D₀ F A₀.N A₀.ν (Set.range fun i => (p i).1.2.b) (Set.finite_range _)
    obtain ⟨O₁, _, N₀, I, hI, hp⟩ := GlobalTheory.T.torsionClasses_descend_finite_algebra O' F S₀ hS₀ A₀.N K₁ A₁ f1 f3 f4 f5 f6 f7 iθ iσ ith (iψ a.gen) (Option Ix) k p
      (fun i => by cases i; exacts [hj, hm2]) fun i => f2 _ ⟨i, rfl⟩
    have : FaithfulSMul O' F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
      rw [IsScalarTower.algebraMap_eq O' (FractionRing O') F]
      exact (algebraMap (FractionRing O') F).injective.comp (IsFractionRing.injective O' _))
    have : Module.Free O' O₁ := Module.free_of_finite_type_torsion_free'
    obtain ⟨R₁, v, w, h⟩ := exists_sums (O := O') O₁.val.toRingHom io (fun x => by
        rw [← hK, ← hio]; rfl) A₀.be.be hm hj (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j))
      (by rw [← Units.val_pow_eq_pow_val, hr.pow (Nat.mul_pos hm2 hj)]; rfl) I hI
      (fun x => by
        obtain ⟨i, e, he⟩ := ht x
        exact hp (some i) _ (((GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' F A₀.arc _ hm2).2.1 _ _).2 ⟨e, he⟩))
      (hp none _ ((A₀.N.qEq_equivalence _).refl _))
    exact ⟨R₁, v, w, fun _ _ => h⟩
  choose R₁ v w hlev using level
  have ext : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [Algebra (FractionRing O') C] (gam : K →+* C),
      (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) →
      (∀ f, ‖gam (algebraMap (PowerSeries O') K f)‖ ≤ 1) → ∃ A' : Lift a C, A'.ν.IntN ∧ A.arc.Over gam A'.arc ∧
        ∃ I : NumD.Hom (gam.comp io) A₀.N A'.N, I.lam = 1 ∧ (∀ y z, A'.be.be (I.e y) (I.e z) = A₀.be.be y z) ∧
          ∀ n x, (A'.q n x).1.1.toAdd = I.e (A₀.q n x).1.1.toAdd ∧ I.Rel (A₀.q n x).1.2 (A'.q n x).1.2 := by
    intro C _ _ _ _ gam h1 h2
    obtain ⟨S, hS⟩ := exists_ball C
    obtain ⟨A', hA', I₁, l₁, r₁, z₁, x₁, q₁⟩ := GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB K C gam
      (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x => (congrArg gam (hK x)).trans (h1 x).symm))
      S (fun x => (hS _).2 (by rw [h1]; exact h2 _)) A
    refine ⟨A', ⟨S, hS, hA'⟩, ⟨I₁, r₁, z₁, fun s y => A'.ν.eX.injective ?_, fun n x _ =>
      ⟨A'.q n x, (q₁ n x).1, (q₁ n x).2, (A'.N.qEq_equivalence _).refl _⟩⟩, homComp I₀ I₁ _ fun _ => rfl, ?_, fun y z => ?_,
      fun n x => ⟨(q₁ n x).1.trans (congrArg I₁.e (q₀ n x).1), homComp_rel _ _ _ _ (q₀ n x).2 (q₁ n x).2⟩⟩
    · change A'.ν.eX (I₁.e (A.ν.eX.symm (s • A.ν.eX y))) = A'.ν.eX (A'.ν.eX.symm (s • A'.ν.eX (I₁.e y)))
      exact ((x₁ _).trans (A.ν.eX.apply_symm_apply _)).trans
        ((A'.ν.eX.apply_symm_apply _).trans (congrArg (s • ·) (x₁ y))).symm
    · change I₁.lam * Units.map _ I₀.lam = 1
      rw [l₁, l₀, map_one, _root_.mul_one]
    · change A'.be.be (I₁.e (I₀.e y)) (I₁.e (I₀.e z)) = _
      rw [A'.be_eq, A₀.be_eq, x₁, x₁, x₀, x₀]
  have hrm : ∀ m j, Odd m → 0 < j → r (m ^ 2) = r (m ^ 2 * j) ^ j ∧ r j = r (m ^ 2 * j) ^ m ^ 2 := fun m j hm hj =>
    ⟨(hr.2 _ _ (pow_pos hm.pos 2) hj).symm, by rw [mul_comm]; exact (hr.2 _ _ hj (pow_pos hm.pos 2)).symm⟩
  refine ⟨⟨⟨inferInstance, hinj, fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x, hK⟩, A, r, hr1,
    ⟨rfl, hr.2⟩, fun m => v m 1 0, w, ?_, ?_⟩⟩
  · intro n j hp ho hu hj S hS
    have hm : Odd (n ^ j) := ho.pow
    obtain ⟨hfin, hmem, hsum⟩ := hlev (n ^ j) 1 0 hm one_pos
    have hvS : ∀ x, v (n ^ j) 1 0 x ∈ S := fun x =>
      mem_of_isIntegral S hS ((Algebra.IsIntegral.isIntegral (⟨_, hmem x⟩ : R₁ (n ^ j) 1 0)).map (R₁ _ _ _).val)
    have key : ∀ e : ℕ, ∃ (C : Type) (_ : NormedField C) (gam : K →+* C) (u : ℝ), 0 < u ∧ u < 1 ∧
        (∀ x, S.valuation (v (n ^ j) 1 0 x) < 1 → ‖gam (v (n ^ j) 1 0 x)‖ < 1 ∧
          (S.valuation (algebraMap (PowerSeries O') K PowerSeries.X) = 1 → ‖gam (v (n ^ j) 1 0 x)‖ ≤ u ^ e)) ∧
        (∃ x, 1 ≤ ‖gam (v (n ^ j) 1 0 x)‖) ∧ ∀ x, ∃ h, u ^ (A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
          (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat ≤ ‖gam (v (n ^ j) 1 0 (x + n ^ (j - 1) • h))‖ := by
      intro e
      obtain ⟨C, _, _, _, _, gam, g1, g2, g3⟩ := GlobalTheory.T.exists_valuedField_valuationCentre_le_pow (PowerSeries O') K PowerSeries.X
        (fun h => not_isUnit_zero (by simpa using h.map PowerSeries.constantCoeff : IsUnit (0 : O')))
        PowerSeries.X_ne_zero _ hfin S hS e
      letI : Algebra (FractionRing O') C := (gam.comp (algebraMap _ K)).toAlgebra
      have h1 : ∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) =
          gam (algebraMap (PowerSeries O') K (PowerSeries.C x)) := fun x => congrArg gam (hK x)
      have hce : CExt O' ⊥ C := ⟨fun x => by rw [h1]; exact g1 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx]; simp⟩
      obtain ⟨A', hN, -, I, hI, hβ, hq⟩ := ext C gam h1 g1
      let r' : ℕ → Cˣ := fun n => Units.map gam.toMonoidHom (r n)
      have hu' : (r' 1 : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) := congrArg gam hr1
      have hu1 : ‖(r' 1 : C)‖ < 1 := hu' ▸ g2
      have hpow : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = r' 1 := by
        rw [← map_pow, hr.pow (pow_pos hm.pos 2), ← hr.1]
      have hn : ‖(n : C)‖ = 1 := by
        obtain ⟨y, hy⟩ := hu.exists_right_inv
        have a1 := hce.1 n
        have a2 := hce.1 y
        have a3 := congrArg (fun x => ‖algebraMap (FractionRing O') C (algebraMap O' _ x)‖) hy
        simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a1 a3
        nlinarith [norm_nonneg (n : C)]
      obtain ⟨qf, hq1, hq2⟩ := (GlobalTheory.T.arcTorsionValues_norms_integral_positive E H D l Xo c W₀ Y O' b ϖ a hB C hce A' hN).2.2 (r' 1) hu1
      choose p hp' using fun x => (existsUnique_twRel A'.be (r' 1) _ hpow (A'.q _ x)).exists
      obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' C A'.arc _ (pow_pos hm.pos 2)
      obtain ⟨c1, c2⟩ := GlobalTheory.T.twist_tx_coset_norm_ge_alt C A'.N _ A'.be (r' 1) _ qf n _ j hp ho hn hj hu1 hpow hq1 hq2
        (GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) O' a.D₀ a.even a.bimult C hce A'.N A'.ν hN n hp ho hn)
        D.La (A'.q _) (eq_zero_of_nsmul D hp.ne_zero) t1 t2 t3 p hp'
      have hv := (hsum C gam g1 g2 A'.N I _ A'.be hI hβ (r' 1) (r' ((n ^ j) ^ 2)) (r' 1) hu'
        (by rw [← (hrm _ 1 hm one_pos).1]; rfl) (by rw [← (hrm _ 1 hm one_pos).2]; rfl) (A'.q _) p (hq _) hp').1
      refine ⟨C, inferInstance, gam, ‖(r' 1 : C)‖, norm_pos_iff.2 (r' 1).ne_zero, hu1,
        fun x hx => hu' ▸ g3 _ (hmem x) hx, by simpa only [hv] using c1, fun x => ?_⟩
      simpa only [hv, (hq _ x).1, hβ] using c2 x
    have hlt : ∀ x, S.valuation (v (n ^ j) 1 0 x) ≠ 1 → S.valuation (v (n ^ j) 1 0 x) < 1 := fun x h =>
      lt_of_le_of_ne ((S.valuation_le_one_iff _).2 (hvS x)) h
    refine ⟨hvS, ?_, fun hXu x => ?_⟩
    · obtain ⟨C, _, gam, u, -, -, k1, ⟨x, hx⟩, -⟩ := key 0
      exact ⟨x, not_not.1 fun h => (k1 x (hlt x h)).1.not_ge hx⟩
    · obtain ⟨C, _, gam, u, u0, u1, k1, -, k2⟩ := key ((A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
        (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat + 1)
      obtain ⟨h, hh⟩ := k2 x
      exact ⟨h, not_not.1 fun hne => (hh.trans ((k1 _ (hlt _ hne)).2 hXu)).not_gt
        (pow_lt_pow_right_of_lt_one₀ u0 u1 (Nat.lt_succ_self _))⟩
  · intro C _ _ _ _ _ gam u h1 g1 hu hu1
    obtain ⟨A', hN, hO, I, hI, hβ, hq⟩ := ext C gam h1 g1
    refine ⟨A', fun n => Units.map gam.toMonoidHom (r n), hN, hO, fun _ => rfl, fun m hm p hp => ?_⟩
    have S := fun j z hj => (hlev m j z hm hj).2.2 C gam g1 (by rw [hu] at hu1; exact hu1) A'.N I _ A'.be hI hβ u
      (Units.map gam.toMonoidHom (r (m ^ 2))) (Units.map gam.toMonoidHom (r j)) hu
      (by rw [← (hrm _ j hm hj).1]; rfl) (by rw [← (hrm _ j hm hj).2]; rfl) (A'.q _) p (hq _) hp
    exact ⟨⟨1, fun x => by rw [Units.val_one, _root_.one_mul]; exact (S 1 0 one_pos).1 x⟩,
      fun j hj z q hq' => (S j z hj).2 (A'.q j z) q (hq j z).1 (hq j z).2 hq'⟩

end GlobalTheory.ArcSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TripleOut

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem exists_secOn_of_pow_one {X : Scheme.{0}} (L : LB X) (V : X.Opens)
    {σ : ∀ j, Γ(X, V ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j)}
    (hσ : σ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V) :
    ∃ θ ∈ secOn L V, ∀ j, X.basicOpen (σ j) ≤ X.basicOpen (θ (j 0)) := by
  have h : ∀ i, L.U i ≤ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U fun _ => i :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  refine ⟨fun i => resG X (inf_le_inf_left V (h i)) (σ fun _ => i), fun i j => ?_, fun j => ?_⟩
  · have e := congrArg (resG X (inf_le_inf (inf_le_inf_left V (h i)) (h j))) (hσ (fun _ => i) (fun _ => j))
    rw [map_mul, rr, rr, rr] at e
    rw [rr, rr, e]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_one]
    exact rr _ _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    intro x hx
    rw [Scheme.basicOpen_res]
    exact ⟨inf_le_inf_left V (LB.wchart_le L _ _ 0) (X.basicOpen_le _ hx), hx⟩

theorem mem_basicOpen_of_valF {K : Type} [Field K] {X : Scheme.{0}} (g : Sp K ⟶ X) {U : X.Opens} (f : Γ(X, U))
    (h : valF g U f ≠ 0) (w : Sp K) : g w ∈ X.basicOpen f :=
  (GlobalTheory.Points.le_preimage_basicOpen_iff g (by_contra fun hn => h (dif_neg hn)) f).2 (isUnit_iff_ne_zero.2 h)
    (x := w) trivial

theorem exists_geomPoint {X : Scheme.{0}} (y : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ X), ∀ w, x w = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun w => by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem hasTheta (Z : ZHOut ρ M U₀ EE) (h : M.HasDiv S.th) : GlobalTheory.Models.HasTheta Z.G Z.L.L := by
  intro z
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x₀, hx₀⟩ := h z
  let W : M.Z.Opens := ⟨_, M.isOpen_setOf_div S.th x₀⟩
  obtain ⟨σ, hσ, -, hne⟩ := Z.theta W x₀ fun _ hz => hz
  obtain ⟨θ, hθ, hle⟩ := exists_secOn_of_pow_one Z.L.L _ hσ
  refine ⟨W, hx₀, θ, hθ, fun y hy => ?_⟩
  obtain ⟨K, _, _, x, hx⟩ := exists_geomPoint y
  obtain ⟨g, j, hg, hv⟩ := hne K x (by rintro _ ⟨w, rfl⟩; rw [hx]; exact hy)
  refine ⟨g (IsLocalRing.closedPoint K), j 0, ?_, hle j ?_⟩
  · exact (Scheme.Hom.comp_apply g Z.G.hom _).symm.trans (hg ▸ hx _)
  · exact mem_basicOpen_of_valF g (σ j) hv _

theorem splitFib (Z : ZHOut ρ M U₀ EE) : GlobalTheory.Models.SplitFib Z.G := by
  intro z
  refine ⟨M.Z.residueField z, inferInstance, Algebra.id _, inferInstance, inferInstance, ?_⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap (M.Z.residueField z) (M.Z.residueField z))) ≫
      M.Z.fromSpecResidueField z = M.Z.fromSpecResidueField z := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h : ∀ f : Sp (M.Z.residueField z) ⟶ M.Z, f = M.Z.fromSpecResidueField z →
      ∃ E : SplitExt (Sp (M.Z.residueField z)), E.IsGt ((Over.pullback f).obj Z.G) := by
    rintro _ rfl
    exact Z.split z
  exact h _ e

section Cube

variable {B U X : Scheme.{0}} {A : Over B} {A' : Over U} {G : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj A']
  [IsCommMonObj A'] [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem pushPt_comp {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) {T : Over U} (x : T ⟶ A') : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem adj_pull {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' b' : A' ⟶ A'} {a b : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (hb : b'.left ≫ p = p ≫ b.left) (c : Pic A.left)
    (H : cubeCls ![fst A A ≫ a, snd A A] c = cubeCls ![fst A A, snd A A ≫ b] c) {T : Over U} (y₁ y₂ : T ⟶ A') :
    cubeCls ![y₁ ≫ a', y₂] (pull p c) = cubeCls ![y₁, y₂ ≫ b'] (pull p c) := by
  let v := lift (pushPt h.1.w y₁) (pushPt h.1.w y₂)
  refine (pull_cubeCls_push h _ _ v (fun i => ?_) c).symm.trans
    ((congrArg (pull v.left) H).trans (pull_cubeCls_push h _ _ v (fun i => ?_) c))
  · fin_cases i
    · exact (pushPt_comp h ha _).trans (by simp [v])
    · simp [v]
  · fin_cases i
    · simp [v]
    · exact (pushPt_comp h hb _).trans (by simp [v])

theorem pull_graph {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (c : Pic A.left) :
    pull p (cubeCls ![𝟙 A, a] c) = cubeCls ![𝟙 A', a'] (pull p c) := by
  have h₁ := pull_cubeCls_push h ![𝟙 A', a'] ![𝟙 A, a] (pushPt h.1.w (𝟙 A'))
    (fun i => by
      fin_cases i
      · simp
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h ha _)) c
  have e : (pushPt h.1.w (𝟙 A')).left = p := Category.id_comp _
  rwa [e] at h₁

variable [IsIntegral X] [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) [Nonempty U] {j : U ⟶ X}
  [IsOpenImmersion j] (semi : IsSemiAbelian G) {φ : A'.left ⟶ G.left} (h : IsGrpPullback A' G j φ)
include hX semi h

theorem adj_extend {a' b' : A' ⟶ A'} {a b : G ⟶ G} [IsMonHom a] [IsMonHom b]
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) (c : Pic G.left)
    (H : ∀ {T : Over U} (y₁ y₂ : T ⟶ A'), cubeCls ![y₁ ≫ a', y₂] (pull φ c) = cubeCls ![y₁, y₂ ≫ b'] (pull φ c)) :
    cubeCls ![fst G G ≫ a, snd G G] c = cubeCls ![fst G G, snd G G ≫ b] c := by
  have := semi.smooth
  have := semi.geomConnected
  have hsm : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
  let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
  have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ A', pushPt h.1.w y' = u ≫ y := fun y =>
    ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨y₁, hy₁⟩ := hy (fst G G)
  obtain ⟨y₂, hy₂⟩ := hy (snd G G)
  let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
  refine pic_ext X hX j (G ⊗ G).hom e.left u.left T'.hom hsm
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
    (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
  · refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
      ((H y₁ y₂).trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
    · fin_cases i
      · simp [pushPt_comp h ha, hy₁]
      · simp [hy₂]
    · fin_cases i
      · simp [hy₁]
      · simp [pushPt_comp h hb, hy₂]
  · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
    congr 1
    funext i
    fin_cases i <;> simp [e]

theorem prim_extend {a' : A' ⟶ A'} {a : G ⟶ G} [IsMonHom a] (ha : a'.left ≫ φ = φ ≫ a.left) (c : Pic G.left)
    (hc : pull (eSec G) c = 0) (H : pull φ c = cubeCls ![𝟙 A', a'] (pull φ c)) : c = cubeCls ![𝟙 G, a] c := by
  have := semi.smooth
  have := semi.geomConnected
  refine pic_ext X hX j G.hom (eSec G) φ A'.hom inferInstance
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _
    (H.trans (pull_graph h ha c).symm) ?_
  refine hc.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
  refine (cubeCls_one (n := 2) _ hc).symm.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp

end Cube

theorem exists_triple : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (act : OAct (NumberField.RingOfIntegers E) ρ.P.A), S.Over₀ M U₀ → (∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L) → ∃ (act' : OAct (NumberField.RingOfIntegers E) Z.G) (h₂ : _) (h₃ : _), (∀ a, ((Over.pullback Z.u₀).map (act.act a)).left ≫ Z.φ = Z.φ ≫ (act'.act a).left) ∧ (GlobalTheory.Models.AbOpen Z.G → GlobalTheory.Models.Good (SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃)) := by
  intro hD o Ω _ _ _ _ S ρ M U₀ EE Z E _ _ _ H act hO hadj hprim
  have := (inferInstance : ArithBase o Ω).ft
  have := (inferInstance : ArithBase o Ω).char
  have := M.locallyOfFiniteType_int
  have hfl := M.flat_int (M.s ≫ spMap (algebraMap ℤ o))
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian (M.s ≫ spMap (algebraMap ℤ o))
  have := ρ.P.isAb.comm
  have : Nonempty U₀.toScheme := hO.ne.to_subtype
  have hd : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨_, _⟩ := ExtUnique.dense_open U₀ hd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian Z.G Z.semi
  let act₀ := Geo.Tor.OAct.pullback Z.u₀ ρ.P.A act
  obtain ⟨act', hact, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback Z.cart act₀ fun x => by
    obtain ⟨e, he, he'⟩ := grpPullback_iso Z.cart (isGrpPullback_pullback Z.G U₀.ι)
    have := act₀.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hD M.Z U₀ U₀.ι ⟨hO.normal, _, inferInstance, hfl⟩ inferInstance inferInstance
      inferInstance inferInstance Z.G Z.G Z.semi Z.semi (e.inv ≫ act₀.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    rw [← he', Category.assoc, ← ExtUnique.pullback_map_left_fst, hF, ← Category.assoc, ← Category.assoc,
      ← Over.comp_left, ← Over.comp_left, Iso.hom_inv_id_assoc]
  have hp := isGrpPullback_pullback ρ.P.A Z.u₀
  have ha : ∀ x, (act₀.act x).left ≫ pullback.fst ρ.P.A.hom Z.u₀ = pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act x).left :=
    fun x => ExtUnique.pullback_map_left_fst _ _
  have hc : pull Z.φ (cls Z.L.L Z.L.isLB) = pull (pullback.fst ρ.P.A.hom Z.u₀) (cls ρ.P.L ρ.P.isLB) :=
    (cls_eq_iff (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _)).2 ⟨Z.w, Z.w_gen⟩
  refine ⟨act', fun b => ?_, ?_, hact, fun h => ⟨h, splitFib Z, hasTheta Z hO.div⟩⟩
  · refine (cls_eq_iff (isLB_cube _ Z.L.isLB) (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB, cls_cube _ Z.L.isLB]
    have := act'.hom b
    have := act'.hom (H.bar b)
    have h₀ := (cls_eq_iff (isLB_cube _ ρ.P.isLB) (isLB_cube _ ρ.P.isLB)).2 (hadj b)
    rw [cls_cube _ ρ.P.isLB, cls_cube _ ρ.P.isLB] at h₀
    refine adj_extend hO.normal Z.semi Z.cart (hact b) (hact (H.bar b)) _ fun y₁ y₂ => ?_
    rw [hc]
    exact adj_pull hp (ha b) (ha (H.bar b)) _ h₀ y₁ y₂
  · refine (cls_eq_iff Z.L.isLB (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB]
    have := act'.hom H.w0
    have h₀ := (cls_eq_iff ρ.P.isLB (isLB_cube _ ρ.P.isLB)).2 hprim
    rw [cls_cube _ ρ.P.isLB] at h₀
    refine prim_extend hO.normal Z.semi Z.cart (hact H.w0) _
      ((cls_eq_zero_iff (pull_isLB Z.L.isLB _)).2 ⟨Z.L.rig, Z.L.rigGen⟩) ?_
    rw [hc]
    exact (congrArg (pull _) h₀).trans (pull_graph hp (ha H.w0) _)

end GlobalTheory.TripleOut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformizationDataCompleteLocalPrimeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformization_data_complete_local_prime : Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen := by
  first | exact @GlobalTheory.PreUnifLocal.exists_preU_local | exact GlobalTheory.PreUnifLocal.exists_preU_local | (intros; apply GlobalTheory.PreUnifLocal.exists_preU_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  first | exact @GlobalTheory.IsoValCocycle.cocycle_eq_val | exact GlobalTheory.IsoValCocycle.cocycle_eq_val | (intros; apply GlobalTheory.IsoValCocycle.cocycle_eq_val <;> assumption)
end

