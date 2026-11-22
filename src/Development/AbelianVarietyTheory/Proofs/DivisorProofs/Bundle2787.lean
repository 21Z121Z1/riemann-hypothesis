import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.LeadTerm

theorem int_bound {X : Type} [AddCommGroup X] (q : X → ℤ) (h0 : ∀ x, 0 ≤ q x) (hz : q 0 = 0)
    (hneg : ∀ a, q (-a) = q a)
    (hcub : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b))
    (m α : X) (j : ℕ) (hj : q α ≤ j) : q α ≤ j * q m + q (m + α) := by
  have hlin : ∀ (n : ℕ) (y : X),
      q (n • m + y) = q (n • m) + q y + n * (q (m + y) - q m - q y) := by
    intro n y
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hcub (n • m) m y
      rw [succ_nsmul]
      push_cast
      linarith
  have h2 : q (m + m) = 4 * q m := by
    have h := hcub m m (-m)
    simp only [add_neg_cancel_right, add_neg_cancel, hneg, hz] at h
    linarith
  have hsq : ∀ n : ℕ, q (n • m) = (n : ℤ) ^ 2 * q m := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hlin n m
      rw [succ_nsmul, h, ih, h2]
      push_cast
      ring
  rcases (h0 m).lt_or_eq with hm | hm
  · have : (j : ℤ) ≤ j * q m := by nlinarith
    linarith [h0 (m + α)]
  · have hB : q α ≤ q (m + α) := by
      by_contra hlt
      push_neg at hlt
      set n : ℕ := (q α).toNat + 1 with hn
      have hnz : (n : ℤ) = q α + 1 := by
        rw [hn]; push_cast; rw [Int.toNat_of_nonneg (h0 α)]
      have h := hlin n α
      rw [hsq n, ← hm] at h
      have hpos := h0 (n • m + α)
      rw [hnz] at h
      nlinarith
    rw [← hm]
    linarith

theorem exists_mul_eq_of_addVal_le {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] (x y : R)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ y) ≤
      IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ x)) :
    ∃ s ∉ P, ∃ a : R, s * x = a * y := by
  obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have hinj := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)
  refine ⟨s, s.2, a, hinj ?_⟩
  have hs := IsLocalization.mk'_spec (Localization.AtPrime P) a s
  rw [map_mul, map_mul, hc, ← hs]
  ring

theorem lead_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax α
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hκ0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_right_cancel (b := κ 0 * κ 0 * κ 0)
      (by simpa only [_root_.mul_assoc, _root_.one_mul] using h)

  have hr : ∀ x, ∃ s : R, (κ x : K) = algebraMap R K s := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, by simp [hx, hκ0]⟩
    · obtain ⟨s, -, hs⟩ := hmax x hx
      exact ⟨s, hs⟩
  choose r hr using hr
  have hr0 : ∀ x, r x ≠ 0 := by
    intro x h
    have := hr x
    rw [h, map_zero] at this
    exact (κ x).ne_zero this
  have hrneg : ∀ a, r (-a) = r a := by
    intro a; apply hinjK; rw [← hr, ← hr, hneg]
  have hrz : r 0 = 1 := by
    apply hinjK; rw [← hr, hκ0]; simp
  have hrcub : ∀ a a' b, r (a + a' + b) * r a * r a' * r b = r (a + a') * r (a + b) * r (a' + b) := by
    intro a a' b
    apply hinjK
    simp only [map_mul, ← hr]
    exact_mod_cast congrArg Units.val (hcub a a' b)

  have hZ : ∀ (j : ℕ) (m : X), ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) =
      algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α) := by
    intro j m
    have hm0 : algebraMap R K (r m) ≠ 0 := by rw [← hr]; exact (κ m).ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hr, map_mul, map_pow]
    field_simp
    ring

  set Φ : Ideal R → ℕ → Prop := fun P j => ∀ m, ∃ s ∉ P, ∃ a : R, s * (r m ^ j * r (m + α)) = a * r α
  have hloc : ∀ P : Ideal R, ∀ hP : P.IsPrime, P.height = 1 →
      ∃ J : ℕ, (r α ∉ P → J = 0) ∧ ∀ j ≥ J, Φ P j := by
    intro P hP h1
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
    set D := Localization.AtPrime P
    have hne : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) ≠ ⊤ := by
      intro x h
      rw [IsDiscreteValuationRing.addVal_eq_top_iff] at h
      exact hr0 x (IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors P)
        (by rw [h, map_zero]))
    set v : X → ℕ := fun x => (IsDiscreteValuationRing.addVal D (algebraMap R D (r x))).toNat
    have he : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) = (v x : ℕ∞) :=
      fun x => (ENat.coe_toNat (hne x)).symm
    have hvz : v 0 = 0 := by
      have := he 0
      rw [hrz, map_one, IsDiscreteValuationRing.addVal_one] at this
      exact_mod_cast this.symm
    have hvneg : ∀ a, v (-a) = v a := by intro a; simp only [v, hrneg]
    have hvcub : ∀ a a' b, v (a + a' + b) + v a + v a' + v b = v (a + a') + v (a + b) + v (a' + b) := by
      intro a a' b
      have := congrArg (fun t => IsDiscreteValuationRing.addVal D (algebraMap R D t)) (hrcub a a' b)
      simp only [map_mul, IsDiscreteValuationRing.addVal_mul, he] at this
      exact_mod_cast this
    refine ⟨v α, fun hα => ?_, fun j hj m => ?_⟩
    · have hu : IsUnit (algebraMap R D (r α)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff D P (r α)).mpr hα
      have := he α
      rw [← hu.unit_spec, IsDiscreteValuationRing.addVal_eq_zero_of_unit] at this
      exact_mod_cast this.symm
    · have hb := int_bound (fun x => (v x : ℤ)) (fun x => by positivity) (by simp [hvz])
        (fun a => by simp [hvneg]) (fun a a' b => by exact_mod_cast hvcub a a' b) m α j
        (by exact_mod_cast hj)
      have hb' : v α ≤ j * v m + v (m + α) := by exact_mod_cast hb
      apply exists_mul_eq_of_addVal_le P
      rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        he, he, he, nsmul_eq_mul]
      exact_mod_cast hb'

  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one (hr0 α)
  have hev : ∀ P ∈ {P : Ideal R | P.IsPrime ∧ P.height = 1 ∧ r α ∈ P},
      ∀ᶠ j in Filter.atTop, Φ P j := by
    rintro P ⟨hP, h1, -⟩
    obtain ⟨J, -, hJ⟩ := hloc P hP h1
    exact Filter.eventually_atTop.mpr ⟨J, hJ⟩
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.eventually_all_finite hfin).mpr hev)
  have hall : ∀ j ≥ J, ∀ P : Ideal R, P.IsPrime → P.height = 1 → Φ P j := by
    intro j hj P hP h1
    by_cases hα : r α ∈ P
    · exact hJ j hj P ⟨hP, h1, hα⟩
    · obtain ⟨J', hJ'0, hJ'⟩ := hloc P hP h1
      exact hJ' j (by rw [hJ'0 hα]; exact Nat.zero_le _)

  have hint : ∀ j ≥ J, ∀ m, ∃ c : R,
      algebraMap R K c = ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) := by
    intro j hj m
    rw [hZ]
    have hα0 : algebraMap R K (r α) ≠ 0 := by rw [← hr]; exact (κ α).ne_zero
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (K := K)
      (algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)) (by
        intro P hP h1
        obtain ⟨s, hs, a, ha⟩ := hall j hj P hP h1 m
        refine ⟨s, hs, a, ?_⟩
        rw [mul_div_assoc', ← map_mul, ha, map_mul, mul_div_cancel_right₀ _ hα0])
    exact ⟨c, hc⟩

  have hstep : ∀ k ≥ J + 2, ∀ m, ∃ c : R,
      ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m * c) := by
    intro k hk m
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, hc⟩ := hint (i - 1) (by omega) m
    refine ⟨c, ?_⟩
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at hc
    rw [pow_succ', _root_.mul_assoc, Units.val_mul, ← hc, map_mul, hr]
  refine ⟨J + 2, fun k hk => ⟨fun m hm => ?_, fun n => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hstep k hk m
    obtain ⟨s, hs, hsκ⟩ := hmax m hm
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩
  · refine (GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R X κ hneg hcub hmax n).subset ?_
    intro m hm hm'
    apply hm
    obtain ⟨s, hs, hsκ⟩ := hm'
    obtain ⟨c, hc⟩ := hstep k hk m
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩

end GlobalTheory.LeadTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8PowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_structure_e8_power : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  first | exact @GlobalTheory.PowE8.exists_cp_e8LB | exact GlobalTheory.PowE8.exists_cp_e8LB | (intros; apply GlobalTheory.PowE8.exists_cp_e8LB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPullbackCocyclesPointValue
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cupZ_pull_apply_fv : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  intro R _ A B m₁ m₂ a b E _ _ E' _ _ E'' _ _ φ ψ z
  have e1 : fv (m₁.coef.pullbackOneCocycle a) E E' φ z = fv a E E' φ (z ≫ fst A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R A (A ⊗ B) (fst A B) m₁ a]; rfl
  have e2 : fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R B (A ⊗ B) (snd A B) m₂ b]; simp only [Fn1.pull, Category.assoc]
  rw [← e1, ← e2, cupZ_apply]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    GlobalTheory.T.bijective_liftSemi_tot0_of_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperIdentificationChainAgreesGenerically
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.tied_chain_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D w₁ w₂ hT c₀ hc R' fg frac hth hev ρ' G _ α β h1 c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ G₂ _
    α₂ β₂ h2
  obtain ⟨mT, pT, bT, tT⟩ := hT
  obtain ⟨m₁, p₁, b₁, t₁⟩ := h1
  obtain ⟨m₂, p₂, b₂, t₂⟩ := h2
  refine ⟨w₂.G, inferInstance, mT ≫ m₁, m₂, ?_, p₂, ?_, ?_⟩
  · exact (pT.comp p₁).congr (Geo.Tor.spMap_comp (ratHull R').val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · rw [Category.assoc, b₁, bT, b₂]
  · intro x
    obtain ⟨w, hw, hw'⟩ := tT x
    obtain ⟨w₁', hw₁, hw₁'⟩ := t₁ x
    obtain ⟨w₂', hw₂, hw₂'⟩ := t₂ (D.lab x)
    have s0 : w ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w _ hw'
    have s1 : w₁' ≫ w₁.G.hom = 𝟙 _ := SameChain.sec_of_pt X₁.ρ w₁.α w₁.hα.1 w₁' _ hw₁
    have s2 : w₂' ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w₂' _ hw₂
    have hwm : w ≫ mT = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁' := by
      apply w₁.hα.1.hom_ext
      · rw [Category.assoc, hw, Category.assoc, hw₁]
      · rw [Category.assoc, pT.1.w, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w = w₂' := by
      apply w₂.hα.1.hom_ext
      · rw [hw', hw₂]
      · rw [s0, s2]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, ← Category.assoc, hwm]
      simp only [Category.assoc]
      rw [hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁), Category.assoc]
    · rw [hwe, hw₂']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_extension_local_domain : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  first | exact @GlobalTheory.SplitPowEight.exists_unif_pow8 | exact GlobalTheory.SplitPowEight.exists_unif_pow8 | (intros; apply GlobalTheory.SplitPowEight.exists_unif_pow8 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleEvenBimultExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.UnitPsi

theorem rescale_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (g' : (GlobalTheory.PolDeg.rescale D g).X → (FractionRing R)ˣ) :
    GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) g' = GlobalTheory.PolDeg.rescale D (fun χ => g' χ * g χ) := by
  unfold GlobalTheory.PolDeg.rescale
  congr 1
  funext χ
  unfold GlobalTheory.UU.scaleGen
  congr 1
  funext j
  have hu : unitOn (g' χ * g χ) = unitOn (g' χ) * unitOn (g χ) := map_mul _ _ _
  change _ * (_ * (D.psi χ).s j) = _
  rw [hu, map_mul, _root_.mul_assoc]

theorem even_step (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧ (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  obtain ⟨h, hh, hE⟩ := GlobalTheory.DefectHom.exists_evenDefect_hom R D hB
  obtain ⟨k, hk3, hkn⟩ := GlobalTheory.T.cubical_function_of_homomorphism D.X (FractionRing R)ˣ (fun a => (h a)⁻¹) (fun a b => by rw [hh, mul_inv])
  refine ⟨k, ?_, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D k).2 hB).2 hk3⟩
  have e := GlobalTheory.PolDeg.evenDefect_rescale D h k hE
  have e1 : (fun χ : D.X => h χ * k (-χ) * (k χ)⁻¹) = fun _ => 1 := by
    funext χ
    rw [hkn χ, mul_inv_cancel_left, mul_inv_cancel]
  rw [e1] at e
  exact (GlobalTheory.PolDeg.evenDefect_one_iff _).1 e

theorem top_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hE : D.PsiEven)
    (hB : D.TauBimult) : ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  obtain ⟨ga, a, hs⟩ := GlobalTheory.exists_psiScal R D
  obtain ⟨h3, h2⟩ := GlobalTheory.PsiScalUnit.main R D ga a hs
  let e : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  have he : Function.Injective e := fun u v e =>
    Units.ext (IsFractionRing.injective R (FractionRing R) (congrArg Units.val e))
  obtain ⟨c, hc3, hce, hci⟩ := GlobalTheory.T.cubical_function_lift_units D.X Rˣ (FractionRing R)ˣ e he a
    (fun x y w => by
      obtain ⟨u, hu⟩ := h3 hB x y w
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
    (fun x => by
      obtain ⟨u, hu⟩ := h2 hE x
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
  exact ⟨c, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).1 hE).2 hce, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).2 hB).2 hc3,
    GlobalTheory.T.psi_scaling_integral_rescale R D ga a hs c hci⟩

theorem exists_rescale_even_bimult_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  intro R _ _ _ _ D
  obtain ⟨g₁, h₁⟩ := GlobalTheory.T.degeneration_rescale_tau_bimult_exists R D
  obtain ⟨g₂, e₂, b₂⟩ := even_step R (GlobalTheory.PolDeg.rescale D g₁) h₁
  obtain ⟨g₃, e₃, b₃, p₃⟩ := top_step R _ e₂ b₂
  refine ⟨fun χ => g₃ χ * g₂ χ * g₁ χ, ?_⟩
  rw [rescale_rescale, rescale_rescale] at e₃ b₃ p₃
  exact ⟨e₃, b₃, p₃⟩

end GlobalTheory.UnitPsi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationPropertiesStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationHomotopyOperator_filtration_properties : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  first | exact @GlobalTheory.PDForm.HotFil.hot_fil | exact GlobalTheory.PDForm.HotFil.hot_fil | (intros; apply GlobalTheory.PDForm.HotFil.hot_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRingStatement
section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  first | exact @GlobalTheory.TaylorInj.taylor_injective | exact GlobalTheory.TaylorInj.taylor_injective | (intros; apply GlobalTheory.TaylorInj.taylor_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_carries_translateChart : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) → ∀ φ, N.Datum φ → ∀ (j : Option (Fin n)) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback G'.hom (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j → z ≫ pullback.snd _ _ = s → z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  first | exact @GlobalTheory.Mum.Near.datum_chart | exact GlobalTheory.Mum.Near.datum_chart | (intros; apply GlobalTheory.Mum.Near.datum_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentInvariantOfChartwiseProjectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentInvariant_of_chartwise_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.descent_eqn_of_chart_projection | exact GlobalTheory.Mum.descent_eqn_of_chart_projection | (intros; apply GlobalTheory.Mum.descent_eqn_of_chart_projection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantPerturbationBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_perturbation_bound : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  first | exact @GlobalTheory.det_sub_lt_of_close_on_unitBall | exact GlobalTheory.det_sub_lt_of_close_on_unitBall | (intros; apply GlobalTheory.det_sub_lt_of_close_on_unitBall <;> assumption)
end

