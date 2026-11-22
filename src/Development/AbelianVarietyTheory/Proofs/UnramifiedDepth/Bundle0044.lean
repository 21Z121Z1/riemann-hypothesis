import Mathlib
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LiftZPMapAeval
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem isUnit_of_isUnit_map_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (x : R') (hx : IsUnit (π x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := hs y
  have h1 : x * y' - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hy]
  have h2 : (x * y' - 1) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  have h3 : IsUnit (x * y' - 1 + 1) := IsNilpotent.isUnit_add_one ⟨2, h2⟩
  rw [sub_add_cancel] at h3
  exact isUnit_of_mul_isUnit_left h3

private theorem ringHom_aeval_eq_aeval_apply {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem exists_root_lift_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (f : ℤ[X]) (z : R)
    (hz : Polynomial.aeval z f = 0) (hd : IsUnit (Polynomial.aeval z (derivative f))) :
    ∃ z' : R', π z' = z ∧ Polynomial.aeval z' f = 0 := by
  obtain ⟨z₀, rfl⟩ := hs z
  have hu : IsUnit (Polynomial.aeval z₀ (derivative f)) :=
    isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ (by rwa [ringHom_aeval_eq_aeval_apply])
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h0 : π (Polynomial.aeval z₀ f) = 0 := by rwa [ringHom_aeval_eq_aeval_apply]
  have h1 : -(v * Polynomial.aeval z₀ f) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_neg, map_mul, h0, mul_zero, neg_zero]
  have h2 : (-(v * Polynomial.aeval z₀ f)) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  refine ⟨z₀ + -(v * Polynomial.aeval z₀ f), ?_, ?_⟩
  · rw [map_add, RingHom.mem_ker.mp h1, add_zero]
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ h2, mul_neg, ← _root_.mul_assoc, hv, _root_.one_mul,
      add_neg_cancel]

private theorem isUnit_aeval_derivative_cyclotomic {R : Type} [CommRing R] (M : ℕ) (hM : M ≠ 0) (hu : IsUnit (M : R))
    (z : R) (hz : Polynomial.aeval z (cyclotomic M ℤ) = 0) :
    IsUnit (Polynomial.aeval z (derivative (cyclotomic M ℤ))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one M ℤ
  have h1 : z ^ M = 1 := by
    have := congrArg (Polynomial.aeval z) hg
    rw [map_mul, hz, zero_mul] at this
    simpa [sub_eq_zero] using this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one h1 hM
  have h2 := congrArg (fun q => Polynomial.aeval z (derivative q)) hg
  simp only [derivative_mul, map_add, map_mul, hz, zero_mul, add_zero, derivative_sub,
    derivative_one, sub_zero, derivative_X_pow, map_natCast, map_pow, aeval_X] at h2
  have h3 : IsUnit ((M : R) * z ^ (M - 1)) := hu.mul (hzu.pow _)
  rw [h2] at h3
  exact isUnit_of_mul_isUnit_left h3

private theorem lift_squareZero_general {B R' R : Type} [CommRing B] [CommRing R'] [CommRing R]
    (π : R' →+* R) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (β : B →+* R) (z' : R') (hz : π z' = β ζ) (hz' : Polynomial.aeval z' f = 0) :
    ∃ β' : B →+* R', π.comp β' = β := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R' := AdjoinRoot.lift (algebraMap ℤ R') z' hz'
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z' g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ ?_
    simpa using (hS n hn).map β
  refine ⟨IsLocalization.lift hu, IsLocalization.ringHom_ext S' ?_⟩
  refine RingHom.ext fun a => ?_
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  rw [halg, hφ, hα, ringHom_aeval_eq_aeval_apply, ringHom_aeval_eq_aeval_apply, hz]

private def liftZP_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem isUnit_natCast_of_mem_denominators (p M n : ℕ) (hn : n ∈ liftZP_S p) : IsUnit (n : ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem exists_mul_eq_aeval_zeta_of_mem (p M : ℕ) (x : ℂ) (hx : x ∈ ZP p M) :
    ∃ n ∈ liftZP_S p, ∃ g : ℤ[X], x * (n : ℂ) = Polynomial.aeval (zeta M) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

theorem zp_lift_sqZero :
  (∀ (p M : ℕ) (R' R : Type) [CommRing R'] [CommRing R] (π : R' →+* R), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → M.Coprime p → M ≠ 0 →
    ∀ β : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R, ∃ β' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R', π.comp β' = β) := by
  intro p M R' R _ _ π hs hk hMp hM β
  have hprim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have hmin : cyclotomic M ℤ = minpoly ℤ (zeta M) :=
    cyclotomic_eq_minpoly hprim (Nat.pos_of_ne_zero hM)
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (zetaZP p M) g : ZP p M) : ℂ)
      = Polynomial.aeval (zeta M) g := fun g => ringHom_aeval_eq_aeval_apply (ZP p M).subtype g _
  have h0 : Polynomial.aeval (zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  have hβ0 : Polynomial.aeval (β (zetaZP p M)) (cyclotomic M ℤ) = 0 := by
    rw [← ringHom_aeval_eq_aeval_apply, h0, map_zero]
  have hMu : IsUnit (M : R) := by simpa using (isUnit_natCast_of_mem_denominators p M M ⟨hM, hMp⟩).map β
  obtain ⟨z', hz, hz'⟩ := exists_root_lift_of_ker_sq_eq_bot π hs hk _ _ hβ0 (isUnit_aeval_derivative_cyclotomic M hM hMu _ hβ0)
  refine lift_squareZero_general π hs hk (cyclotomic M ℤ) (zetaZP p M) (liftZP_S p) h0 ?_
    (isUnit_natCast_of_mem_denominators p M) ?_ β z' hz hz'
  · intro g hg
    rw [hmin]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (Nat.pos_of_ne_zero hM)) ?_
    rw [← hcoe, hg]
    rfl
  · intro b
    obtain ⟨n, hn, g, hg⟩ := exists_mul_eq_aeval_zeta_of_mem p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNondegenerateIntegralTorsion
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section Transfer
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

private theorem pfTie_prod1 {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift (x * x') y).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x' y).left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2) = CartesianMonoidalCategory.lift (x * x') y := by
    rw [comp_lift]
    congr 1
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
    · simp [x3]
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2) = CartesianMonoidalCategory.lift x' y := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_prod2 {T : Over S} (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift x (y * y')).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x y').left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = CartesianMonoidalCategory.lift x (y * y') := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y' := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_gen {T : Over S} (x y : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 4) ![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] ![1, -1, -1, 1]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        val t ρ.left z J = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ 0) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ 0)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen P (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => ((hv _ _ z J hJ).trans (val_one _)).trans (by simp)⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ (n + 1)) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left,
        (CartesianMonoidalCategory.lift x (y ^ (n + 1))).left, (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := ULift.{0} (Fin 3) ⊕ ULift.{0} (Fin 3)) (U := U) _
          (c := ∏ i, h ((![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
            (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] : Fin 4 → _) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i) rfl
          (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := ULift.{0} (Fin 3)) (U := U) _ (pfTie_prod1 (x ^ n) x y h)
            (DVR.prod_neg _ _ (pfTie_prod2 x (y ^ n) y h)))).trans ?_
        rw [pow_succ x, pow_succ y]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen P _ _ _ _ t (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left)
        (LB.invGen P _ _ (LB.pullGen P _ _ β.law2 (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    have p₁ : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n := map_pow (preHom ρ) _ _
    have p₂ : ρ ≫ (y ^ n) = (ρ ≫ y) ^ n := map_pow (preHom ρ) _ _
    have q₁ : ρ.left ≫ (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left = (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ n) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₁]
    have q₂ : ρ.left ≫ (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left = (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ n) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₂]
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (congrArg (val β.law1 · z J) q₁))
        ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans (congrArg (val β.law2 · z J) q₂))))))))).trans ?_
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_inv, _root_.mul_mul_mul_comm]

private theorem pfTie_unit {T : Over S} (x y : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        gm ρ.left z ⊤ a = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  obtain ⟨u, hu, hw⟩ := pfTie_gen β x y n
  obtain ⟨t, -, hv⟩ := exists_gen β.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      rw [hx, hy]
      simp [Fin.prod_univ_succ]) u hu
  have le : (⊤ : T.left.Opens) ≤ LB.wchart P (PEmpty.elim : PEmpty → (T.left ⟶ (G ⊗ G).left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  rw [← hw T' ρ z J hJ, ← hv _ _ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)]
  exact gm_res ρ.left z le trivial _

private theorem pfTie_local (R : Type) [CommRing R] [IsLocalRing R] (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ)
    (h : gm (𝟙 (Spec (CommRingCat.of R))) (IsLocalRing.closedPoint R) ⊤ a = 1) : a = 1 := by
  apply Units.ext
  have e := congrArg (fun u => (stalkClosedPointIso (CommRingCat.of R)).hom.hom (Units.val u)) h
  have g := congrArg (fun q => q.hom a.val) (germ_stalkClosedPointIso_hom (CommRingCat.of R))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at g
  have e' : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val = 1 :=
    g.symm.trans ((congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gm_val (𝟙 _) _ ⊤ trivial a)).symm.trans
      (e.trans (map_one _)))
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e'.trans (map_one _).symm)

end Transfer

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem pairing_nondegenerate_integral_torsion :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (b : ∀ R x y, B.P R x y)
    (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
    (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) →
    (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) →
    (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y'))) →
    ∀ (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), p ≠ 0 → v.Integers (O : Type) → Smooth G.hom →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := R₀) C) ≫ x) (fst G (sp (R₀ := R₀) C))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : B.G O, p • x = 0 → (∀ y : B.G O, p • y = 0 → B.IsPairing p x y 1) → x = 0) := by
  intro FRM PFF TORS BIV R₀ _ G _ _ P β B e b J hb hadd _ hJ h1 h2 O C _ _ _ v _ _ _ p hp hv hsm hfin hfl hsurj hnd x hx H
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := Nat.exists_eq_succ_of_ne_zero hp
  have e0 : e O 0 = 1 := by
    have := hadd O 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have en : ∀ (k : ℕ) (w : B.G O), e O (k • w) = e O w ^ k := fun k w => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero, e0]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨j, hj⟩ : ∃ j : sp (R₀ := R₀) C ⟶ sp (R₀ := R₀) (O : Type), j = spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) :=
    ⟨_, rfl⟩
  have T := (TORS G O C v (N + 1) hv hfin hsurj).2
  rw [← hj] at T
  have hxp : e O x ^ (N + 1) = 1 := by rw [← en, hx, e0]
  have j1 : j ≫ (1 : sp (R₀ := R₀) (O : Type) ⟶ G) = 1 := map_one (preHom j)
  have key : j ≫ e O x = 1 := by
    refine PFF _ G P β C (Spec.map (CommRingCat.ofHom (algebraMap R₀ C))) (N + 1) (Nat.cast_ne_zero.2 hp) hsm hfin hfl
      hsurj hnd (j ≫ e O x) ((map_pow (preHom j) _ _).symm.trans ((congrArg (j ≫ ·) hxp).trans j1))
      (fun y hy z Jc hJc => ?_)
    obtain ⟨y₀, ⟨hy₀, rfl⟩, -⟩ := T y hy
    obtain ⟨y', rfl⟩ := (hb O).2 y₀
    have hy' : (N + 1) • y' = 0 := (hb O).1 (by rw [en, hy₀, e0])
    have F := (((FRM B b _ _ h1 h2).1 O N x y' 1).1 (H y' hy')).2.2
    obtain ⟨a₁, -, a₂, -, -⟩ := BIV _ G P β (sp (R₀ := R₀) (O : Type)) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    have b₁ := a₁ 1 1 (e O x) (e O y')
    have b₂ := a₂ (e O x) 1 1 (e O y')
    simp only [_root_.one_mul] at b₁ b₂
    have c₁ := mul_left_cancel b₁
    have c₂ := mul_left_cancel b₂
    obtain ⟨a, ha⟩ := pfTie_unit β (e O x) (e O y') (N + 1) hxp hy₀
    have a1 : a = 1 := by
      apply pfTie_local (O : Type) a
      have g := ha _ (𝟙 _) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      refine Eq.trans g ?_
      simp only [Category.id_comp]
      rw [Finset.prod_range_succ', Finset.prod_range_succ', pow_zero, pow_zero, ← c₁, ← c₂, mul_inv_eq_one]
      simp only [en, e0] at F
      rw [← map_prod, ← map_prod, ← map_mul, ← map_mul, eq_comm, div_eq_one] at F
      have inj := Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of (O : Type))).hom.hom.toMonoidHom)
        (stalkClosedPointIso (CommRingCat.of (O : Type))).commRingCatIsoToRingEquiv.injective F
      exact (mul_comm _ _).trans (inj.trans (mul_comm _ _))
    have g := ha _ j z Jc hJc
    rw [a1, map_one, eq_comm, mul_inv_eq_one] at g
    exact g
  obtain ⟨w, -, hw⟩ := T 1 (one_pow _)
  exact (hb O).1 (((hw _ ⟨hxp, key⟩).trans (hw 1 ⟨one_pow _, j1⟩).symm).trans e0.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsDivisibleAndTorsionOfValuationIntegers
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩

private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]

private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem points_divisible_and_torsion_of_valuation_integers :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this

end GlobalTheory
end

