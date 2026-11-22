import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem GlobalTheory.grpPullback_lift_torsion : ∀ (S S' : Scheme.{0}) (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (T : Over S') (w : Over.mk (T.hom ≫ f) ⟶ G),
      ∃ σ : T ⟶ G', σ.left ≫ φ = w.left ∧ ∀ k : ℕ, w ^ k = 1 → σ ^ k = 1 := by
  intro S S' G' _ G _ f φ h T w
  have uniq : ∀ a b : T ⟶ G', a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    ext
    exact h.1.hom_ext e (by rw [Over.w a, Over.w b])
  let push : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w x])
  have push_left : ∀ x : T ⟶ G', (push x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y : T ⟶ G', push (x * y) = push x * push y := by
    intro x y
    ext
    exact (h.2 T x y (push x) (push y) rfl rfl).symm
  have hone : push 1 = 1 := by
    have e : push 1 * push 1 = push 1 := by rw [← hmul, _root_.mul_one]
    simpa using e
  have hpow : ∀ (x : T ⟶ G') (k : ℕ), push (x ^ k) = push x ^ k := by
    intro x k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, pow_succ, hmul, ih]
  let σ : T ⟶ G' := Over.homMk (h.1.lift w.left T.hom (by simpa using Over.w w)) (h.1.lift_snd _ _ _)
  have hσ : σ.left ≫ φ = w.left := h.1.lift_fst _ _ _
  have hpσ : push σ = w := by ext; exact hσ
  refine ⟨σ, hσ, fun k hk => uniq _ _ ?_⟩
  rw [← push_left, ← push_left, hpow, hpσ, hk, hone]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoiding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem isJacobsonRing_int_of_dim_one : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_trait_finite_residueField_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  intro B _ _ _ _ m h hm hh
  classical

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int_of_dim_one
  haveI : Algebra.FiniteType ℤ (B ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m)
  set p := ringChar (B ⧸ m) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (B ⧸ m) 0 := h0 ▸ ringChar.charP (B ⧸ m)
    haveI : CharZero (B ⧸ m) := CharP.charP_to_charZero _
    haveI : Algebra.IsIntegral ℤ (B ⧸ m) := Algebra.IsIntegral.of_finite ℤ _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (algebraMap ℤ (B ⧸ m)).injective_int (Field.toIsField _))
  haveI : CharP (B ⧸ m) p := ringChar.charP (B ⧸ m)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) p).resolve_right hp0⟩
  letI : Algebra (ZMod p) (B ⧸ m) := ZMod.algebra (B ⧸ m) p
  haveI : IsScalarTower ℤ (ZMod p) (B ⧸ m) := AddCommGroup.intIsScalarTower
  haveI : Algebra.FiniteType (ZMod p) (B ⧸ m) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (B ⧸ m)
  haveI : Module.Finite (ZMod p) (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing (ZMod p) (B ⧸ m)
  haveI hfin : Finite (B ⧸ m) := Module.finite_of_finite (ZMod p)
  have hpm : (p : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let R := Localization.AtPrime m
  haveI hRn : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors m)
  have hx0 : algebraMap B R (h * p) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B R)]; exact fun e => mul_ne_zero hh hpB (hinj e)
  have hxm : algebraMap B R (h * p) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R m _).mpr (m.mul_mem_left h hpm)
  obtain ⟨q, hq, hnq, hdim⟩ := GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one R (algebraMap B R (h * p)) hx0 hxm
  let D := R ⧸ q
  haveI : IsDomain D := Ideal.Quotient.isDomain q
  haveI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let φ : B →+* D := (Ideal.Quotient.mk q).comp (algebraMap B R)
  have hcompR : Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hcomp : Ideal.comap φ (IsLocalRing.maximalIdeal D) = m := by
    rw [← Ideal.comap_comap, hcompR]; exact Localization.AtPrime.comap_maximalIdeal
  have hφh : φ h ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_right _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  have hφp : φ (p : B) ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_left _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  haveI hD0 : CharZero D := by
    haveI : CharP D (ringChar D) := ringChar.charP D
    rcases CharP.char_is_prime_or_zero D (ringChar D) with hl | hl
    · exfalso
      have hlm' : ((ringChar D : ℕ) : B) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal D) := by
        rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]; exact zero_mem _
      have hlm : ((ringChar D : ℕ) : B) ∈ m := hcomp.le hlm'
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hlm
      have hdvd : p ∣ ringChar D := (CharP.cast_eq_zero_iff (B ⧸ m) p _).mp hlm
      have hpl : p = ringChar D :=
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).mp hdvd)
      apply hφp; rw [map_natCast, hpl, CharP.cast_eq_zero]
    · haveI : CharP D 0 := hl ▸ ringChar.charP D
      exact CharP.charP_to_charZero D

  have hsurj : Function.Surjective ((IsLocalRing.residue D).comp φ) := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hsR := IsLocalization.surjective_quotientMap_of_maximal_of_localization m.primeCompl R
      (I := IsLocalRing.maximalIdeal R) (J := m)
      (H := le_of_eq Localization.AtPrime.comap_maximalIdeal.symm)
      (by rw [Localization.AtPrime.comap_maximalIdeal]; exact hm)
    obtain ⟨bb, hb⟩ := hsR (Ideal.Quotient.mk _ r)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bb
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hb
    simp only [RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hb' : algebraMap B R b - r ∈ Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) :=
      hcompR ▸ hb
    simpa [φ, map_sub] using hb'
  have hker : ∀ b ∈ m, ((IsLocalRing.residue D).comp φ) b = 0 := by
    intro b hb
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hcomp]; exact hb
  haveI hresfin : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_surjective (Ideal.Quotient.lift m _ hker) (by
      intro y; obtain ⟨b, rfl⟩ := hsurj y; exact ⟨Ideal.Quotient.mk m b, rfl⟩)
  obtain ⟨V, _, _, _, hcV, g, hg, hgl, hVfin⟩ :=
    GlobalTheory.exists_complete_dvr_finite_residueField D inferInstance hdim hresfin
  haveI : CharZero V := ⟨fun a b e => by
    apply Nat.cast_injective (R := D); apply hg; rw [map_natCast, map_natCast]; exact e⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, g.comp φ, hcV, hVfin, ?_, ?_⟩
  · rw [RingHom.comp_apply]; intro e; apply hφh; apply hg; rw [e, map_zero]
  · have hgm : Ideal.comap g (IsLocalRing.maximalIdeal V) = IsLocalRing.maximalIdeal D := by
      ext x; simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    rw [← Ideal.comap_comap, hgm, hcomp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransport

variable {S' Z : Scheme.{0}} {π : S' ⟶ Z} {M : LB Z} {L : LB S'} {N : ℕ}

theorem w_trans (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ S') (y : Y)
    (i i' : L.ι) (k k' : M.ι) (hi : f y ∈ L.U i) (hi' : f y ∈ L.U i') (hk : (f ≫ π) y ∈ M.U k)
    (hk' : (f ≫ π) y ∈ M.U k') :
    gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y (L.U i ⊓ L.U i') (L.g i i') ^ (N : ℤ) * (gm (f ≫ π) y (M.U k ⊓ M.U k') (M.g k k'))⁻¹ *
        gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) := by
  have m1 : f y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have m1' : f y ∈ (lbPow L N).U (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have m2 : f y ∈ (M.pull π).U (fun _ => k) := Set.mem_iInter.2 fun _ => hk
  have m2' : f y ∈ (M.pull π).U (fun _ => k') := Set.mem_iInter.2 fun _ => hk'
  have hm : f y ∈ (lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) := ⟨⟨m1, m2⟩, ⟨m1', m2'⟩⟩
  have e := congrArg (gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')))) (hw (fun _ => i, fun _ => k) (fun _ => i', fun _ => k'))
  have e1 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_left (w.s (fun _ => i, fun _ => k))) :=
    (gm_res f y _ hm _).symm
  have e2 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_right (w.s (fun _ => i', fun _ => k'))) =
      gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) :=
    gm_res f y _ hm _
  have e3 := gm_div (M.pull π) (lbPow L N) f y (fun _ => i, fun _ => k) (fun _ => i', fun _ => k') hm
  refine e1.trans (e.trans ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·) (e3.trans ?_) e2)))
  exact congrArg₂ (fun a b => a * b⁻¹)
    ((gm_linComb L (fun _ => 𝟙 S') (fun _ => (N : ℤ)) f y (fun _ => i) (fun _ => i') m1 m1').trans
      (by rw [Fintype.prod_unique, Category.comp_id]))
    (gm_pull_g M π f y (fun _ => k) (fun _ => k') m2 m2')

theorem alg₁ {G : Type*} [CommGroup G] (t E W : G) (N : ℕ) :
    (t * E) ^ N * (t ^ (N : ℤ) * 1⁻¹ * W)⁻¹ = E ^ N * W⁻¹ := by
  rw [zpow_natCast, inv_one, _root_.mul_one, _root_.mul_pow, _root_.mul_inv, _root_.mul_comm (t ^ N),
    _root_.mul_assoc, mul_inv_cancel_left]

theorem alg₂ {G : Type*} [CommGroup G] (E g W : G) (N : ℕ) :
    E ^ N * ((1 : G) ^ (N : ℤ) * g⁻¹ * W)⁻¹ = g * (E ^ N * W⁻¹) := by
  rw [one_zpow, _root_.one_mul, _root_.mul_inv, inv_inv, _root_.mul_left_comm]

theorem exists_strictHenselian_absolutely_closed_local_ring (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen)
    {A : Scheme.{0}} (a : A ⟶ S') (e : LB.Gen (L.pull a)) (he : e.IsGen) :
    ∃ t : LB.Gen (M.pull (a ≫ π)), t.IsGen ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι) (k : M.ι),
      (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z ((M.pull (a ≫ π)).U (fun _ => k)) (t.s (fun _ => k)) =
        gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
  have loc : ∀ k : M.ι, ∃ s : Γ(A, (M.pull (a ≫ π)).U (fun _ => k))ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y)
      (i : L.ι), (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z _ s = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
    intro k
    let V := (M.pull (a ≫ π)).U (fun _ => k)
    let W : L.ι → A.Opens := fun i => V ⊓ (L.pull a).U (fun _ => i)
    have h1 : ∀ i, W i ≤ (L.pull a).U (fun _ => i) := fun i => inf_le_right
    have h2 : ∀ i, W i ≤ a ⁻¹ᵁ ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) := fun i x hx =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.2 (), Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 ()⟩
    let u : ∀ i, Γ(A, W i)ˣ := fun i =>
      res (h1 i) (e.s (fun _ => i)) ^ N * (res (h2 i) (pullU a _ (w.s (fun _ => i, fun _ => k))))⁻¹
    have hu : ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι), r z ∈ W i →
        gm r z (W i) (u i) = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
      intro Y r z i hz
      simp only [u, map_mul, map_pow, map_inv]
      exact congrArg₂ (fun p q => p ^ N * q⁻¹) (gm_res r z (h1 i) hz _)
        ((gm_res r z (h2 i) hz _).trans (gm_pull r a z _ (h2 i hz) _))
    obtain ⟨s, hs⟩ := glue_unit V W (fun i => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL (a x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩) u
      (fun i j x hx => by
        have hi : (𝟙 A ≫ a) x ∈ L.U i := Set.mem_iInter.1 hx.1.2 ()
        have hj : (𝟙 A ≫ a) x ∈ L.U j := Set.mem_iInter.1 hx.2.2 ()
        have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U k := Set.mem_iInter.1 hx.1.1 ()
        have g1 : gm (𝟙 A) x ((L.pull a).U fun _ => i) (e.s fun _ => i) =
            trF (fun _ : PUnit => a) (fun _ => 1) (𝟙 A) x (fun _ => i) (fun _ => j) *
              gm (𝟙 A) x ((L.pull a).U fun _ => j) (e.s fun _ => j) := gen_trans he (𝟙 A) x hx.1.2 hx.2.2
        rw [hu A (𝟙 A) x i hx.1, hu A (𝟙 A) x j hx.2, g1,
          w_trans w hw (𝟙 A ≫ a) x i j k k hi hj hk hk, gm_self hM _ x hk]
        simp only [trF, Fintype.prod_unique, zpow_one]
        exact alg₁ _ _ _ N)
    refine ⟨s, fun Y r z i hi hk => ?_⟩
    have hz : r z ∈ W i := ⟨Set.mem_iInter.2 fun _ => hk, Set.mem_iInter.2 fun _ => hi⟩
    rw [← gm_res r z (inf_le_left : W i ≤ V) hz, hs i, hu Y r z i hz]
  choose s hs using loc
  refine ⟨⟨fun k => s (k ())⟩, fun k k' => unit_ext fun x hx => ?_, fun Y r z i k hi hk => hs k Y r z i hi hk⟩
  refine (gm_res (𝟙 A) x _ hx _).trans (Eq.trans ?_ ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_pull_g M (a ≫ π) (𝟙 A) x k k' hx.1 hx.2) (gm_res (𝟙 A) x _ hx _))).symm)
  obtain ⟨i, hi⟩ := exists_chart hL ((𝟙 A ≫ a) x)
  have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k ()) := Set.mem_iInter.1 hx.1 ()
  have hk' : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k' ()) := Set.mem_iInter.1 hx.2 ()
  have v1 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k) (s (k ())) = _ := hs (k ()) A (𝟙 A) x i hi hk
  have v2 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k') (s (k' ())) = _ := hs (k' ()) A (𝟙 A) x i hi hk'
  rw [v1, v2, w_trans w hw (𝟙 A ≫ a) x i i (k ()) (k' ()) hi hi hk hk', gm_self hL (𝟙 A ≫ a) x hi, Category.assoc]
  exact alg₂ _ _ _ N

theorem transport : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  intro S' Z π M L N hM hL hw0
  obtain ⟨w, hw⟩ := hw0
  classical
  refine ⟨fun A a e => if he : e.IsGen then (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose else ⟨fun _ => 1⟩,
    fun A a e he => ?_, ?_⟩
  · simp only [dif_pos he]
    exact (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.1
  · intro A A' Y a a' e e' r r' he he' hr hval z J hJ
    simp only [dif_pos he, dif_pos he']
    have hk : (r ≫ a ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hJ _
    have hk'e : J (r' ≫ a' ≫ π) = J (r ≫ a ≫ π) := by rw [← Category.assoc, ← hr, Category.assoc]
    have hk' : (r' ≫ a' ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hk'e ▸ hJ _
    obtain ⟨i, hi⟩ := exists_chart hL ((r ≫ a) z)
    have hi' : (r' ≫ a') z ∈ L.U i := by rw [← hr]; exact hi
    obtain ⟨JL, hJL, eJL⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ a) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hi)
    have v1 := val_of (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z JL (fun _ => i) (fun _ => eJL ())
    have v2 := val_of (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z JL (fun _ => i)
      (fun _ => by rw [← hr]; exact eJL ())
    have hv := hval z JL hJL
    rw [v1, v2] at hv
    rw [val_of (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) _ r z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => rfl),
      val_of (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) _ r' z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => hk'e),
]
    refine (((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.2 Y r z i _ hi hk).trans ?_).trans
      ((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a' e' he').choose_spec.2 Y r' z i _ hi' hk').symm
    rw [hr]
    congr 1
    exact congrArg (· ^ N) hv

end GlobalTheory.GenTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTupleThetaConstantRatiosGenerateFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tuple_thetaConstant_ratios_generate_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.thetaSys_gen_tuple | exact GlobalTheory.ZH.thetaSys_gen_tuple | (intros; apply GlobalTheory.ZH.thetaSys_gen_tuple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  first | exact @GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | exact GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | (intros; apply GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  first | exact @GlobalTheory.TorusLift.exists_sec_sq_eq_one | exact GlobalTheory.TorusLift.exists_sec_sq_eq_one | (intros; apply GlobalTheory.TorusLift.exists_sec_sq_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationPullbackToPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem g_eq_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') : D'.P.g = D.P.g :=
  H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.P.smoothDim)
    (eSec D'.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))

theorem exists_pull_of_deg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  intro R R' _ _ _ _ I I' hR hR' g hg hI D D' hD A G _ _ hG U
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨U', -, -, hPU⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg
    GlobalTheory.abelianSchemeLaws_all.1.polBaseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R' I I' hR hR' g hI D A G hG U D' hD (g_eq_of_isPullDeg hD) ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨A', U', hPU⟩

end GlobalTheory.Mum.UnifPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGlueMapsOpenCoverSameSource
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueDesc

theorem exists_unique_glue : ∀ (X Y P : Scheme.{0}) (J : Type) (e : J → (P ⟶ X)) (g : J → (P ⟶ Y)), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ P), a ≫ e i = b ≫ e j → a ≫ g i = b ≫ g j) → ∃ β : X ⟶ Y, (∀ j, e j ≫ β = g j) ∧ ∀ β' : X ⟶ Y, (∀ j, e j ≫ β' = g j) → β' = β := by
  intro X Y P J e g he hcov hcomp
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => P) e (fun x => by
    obtain ⟨j, y, hy⟩ := hcov x
    exact ⟨j, y, hy⟩)
  have hm : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => hcomp i j _ _ _ pullback.condition
  refine ⟨𝒰.glueMorphisms g hm, fun j => 𝒰.ι_glueMorphisms g hm j, fun β' hβ' => ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  change e j ≫ β' = e j ≫ _
  rw [hβ' j]
  exact (𝒰.ι_glueMorphisms g hm j).symm

end GlobalTheory.GlueDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReductionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, MvPolynomial.coeff m G ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  first | exact @GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | exact GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal | (intros; apply GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal <;> assumption)
end

