import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.QHypPull

theorem sq_comm {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) {X : Scheme.{0}} (u' : X ⟶ (A' ⊗ A').left)
    (u : X ⟶ (A ⊗ A).left)
    (h1 : u' ≫ (fst A' A').left ≫ φ = u ≫ (fst A A).left) (h2 : u' ≫ (snd A' A').left ≫ φ = u ≫ (snd A A).left) :
    u' ≫ φ₂ = u := by
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, h1]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, h2]

end GlobalTheory.ActFin.QHypPull

open GlobalTheory.ActFin.QHypPull in

theorem GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  intro S S' f A _ _ A' _ φ φ₂ Q h hs hQ
  obtain ⟨hA, hL, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hsym, hD⟩ := hQ
  haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback S S' A A' f φ h
  have hone : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    rw [GlobalTheory.FlatModel.LiftW.one_left_comp_of_isGrpPullback h A', GlobalTheory.FlatModel.LiftW.one_left_eq,
      GlobalTheory.FlatModel.LiftW.one_left_eq, ← Category.assoc, h.1.w]
    rfl
  have fl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (fst A' A').left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (snd A' A').left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have fl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (fst A A).left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (snd A A).left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have e₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, hone, Category.assoc, fl'])
      (by rw [← Category.assoc, sl, Category.assoc, sl']; rfl)
  have e₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl']; rfl)
      (by rw [← Category.assoc, sl, hone, Category.assoc, sl'])
  have e₃ : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl', hs.2])
      (by rw [← Category.assoc, sl, Category.assoc, sl', hs.1])
  haveI := hA.proper
  refine ⟨⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩,
    pull_isLB hL φ₂, ?_, ?_, ?_, ?_⟩
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (1 : A' ⟶ A') (𝟙 A')).left)
      (fun _ => (lift (1 : A ⟶ A) (𝟙 A)).left) (fun _ => 1) φ (fun _ => e₁)) t₁ ht₁
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (𝟙 A') (1 : A' ⟶ A')).left)
      (fun _ => (lift (𝟙 A) (1 : A ⟶ A)).left) (fun _ => 1) φ (fun _ => e₂)) t₂ ht₂
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q φ₂ φ₂ rfl) (chartPullLinComb Q φ₂
      (fun _ : PUnit => (lift (snd A' A') (fst A' A')).left) (fun _ => (lift (snd A A) (fst A A)).left)
      (fun _ => 1) φ₂ (fun _ => e₃)) hsym
  · exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull S S' A hA Q hL hD f A' φ φ₂ h.1 hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_level_over_cyclotomic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  first | (exact @GlobalTheory.HTSympCover.exists_galoisCover) | (exact GlobalTheory.HTSympCover.exists_galoisCover) | (intros; apply GlobalTheory.HTSympCover.exists_galoisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateHomQTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoByTwo

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A : AbVar K) : A ⟶ prod A A := prodLift (𝟙 A) 0

def inr (A : AbVar K) : A ⟶ prod A A := prodLift 0 (𝟙 A)

end GlobalTheory.TwoByTwo

namespace GlobalTheory.TwoByTwo

end GlobalTheory.TwoByTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateHomSurjectiveOfProduct
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped TensorProduct

namespace GlobalTheory.AV.ProdRed

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def inl (A B : AbVar K) : A ⟶ prod A B := prodLift (𝟙 A) 0

def inr (A B : AbVar K) : B ⟶ prod A B := prodLift 0 (𝟙 B)

def restr (A B : AbVar K) : (prod A B ⟶ prod A B) →ₗ[ℤ] (A ⟶ B) :=
  (AddMonoidHom.mk' (fun f => inl A B ≫ f ≫ prodSnd A B) fun f g => by
    simp only [Preadditive.add_comp, Preadditive.comp_add]).toIntLinearMap

end GlobalTheory.AV.ProdRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateCoker

variable {l : ℕ} [hl : Fact l.Prime] {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)

def lker (l : ℕ) : Subgroup M where
  carrier := {x | φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, m', hm'⟩
    refine ⟨by rw [map_mul, ha, hb, _root_.one_mul], m + m', ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, mul_comm (l ^ m), pow_mul, hm', one_pow, _root_.one_mul]
  one_mem' := ⟨map_one φ, 0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm⟩
    exact ⟨by rw [map_inv, ha, inv_one], m, by rw [inv_pow, hm, inv_one]⟩

theorem pow_pow_eq_one {x : M} {m : ℕ} (h : x ^ l ^ m = 1) (j : ℕ) : x ^ l ^ (m + j) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

variable {φ}

theorem kill [Finite φ.ker] {k : M} (hk : φ k = 1) {m : ℕ} (hm : k ^ l ^ m = 1) :
    k ^ l ^ Nat.card φ.ker = 1 := by
  have hp : l.Prime := hl.out
  have h1 : orderOf k ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hm)
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have h2 : j ≤ Nat.card φ.ker :=
    ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hpos (hj ▸ h1))).le
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow l h2)

theorem exists_lift (hs : Function.Surjective φ) [Finite φ.ker] (n : ℕ) (y : N) (hy : y ^ l ^ n = 1) :
    ∃ x : M, φ x = y ∧ ∃ m : ℕ, x ^ l ^ m = 1 := by
  have hp : l.Prime := hl.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hy
    exact ⟨1, by rw [map_one, hy], 0, one_pow _⟩
  obtain ⟨x₀, rfl⟩ := hs y
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hk : x₀ ^ l ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hc : (x₀ ^ l ^ n) ^ Nat.card φ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' l hp.one_lt.ne'
  have hcop : Nat.Coprime u (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' hp.one_lt)
  refine ⟨x₀ ^ (u * w), ?_, n + e, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hy, hw, pow_one]
  · rw [← pow_mul, show u * w * l ^ (n + e) = l ^ n * Nat.card φ.ker * w by rw [hcu, pow_add]; ring,
      pow_mul, pow_mul, hc, one_pow]

theorem indep [Finite φ.ker] {x x' : M} (h : φ x = φ x') {m m' : ℕ} (hx : x ^ l ^ m = 1)
    (hx' : x' ^ l ^ m' = 1) : x ^ l ^ Nat.card φ.ker = x' ^ l ^ Nat.card φ.ker := by
  have h1 : φ (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (x * x'⁻¹) ^ l ^ (m + m') = 1 := by
    rw [mul_pow, inv_pow, pow_pow_eq_one hx, add_comm, pow_pow_eq_one hx', inv_one, _root_.one_mul]
  have h3 := kill h1 h2
  rwa [mul_pow, inv_pow, mul_inv_eq_one] at h3

variable (hs : Function.Surjective φ) [Finite φ.ker]
include hs

def lift (t : Tate l N) (n : ℕ) : M := (exists_lift hs n (t.lev n) (t.lev_pow n)).choose

theorem lift_spec (t : Tate l N) (n : ℕ) : φ (lift hs t n) = t.lev n ∧ ∃ m : ℕ, lift hs t n ^ l ^ m = 1 :=
  (exists_lift hs n (t.lev n) (t.lev_pow n)).choose_spec

def del (t : Tate l N) : M := lift hs t (Nat.card φ.ker) ^ l ^ Nat.card φ.ker

theorem del_eq (t : Tate l N) {x : M} (hx : φ x = t.lev (Nat.card φ.ker)) {m : ℕ} (hm : x ^ l ^ m = 1) :
    del hs t = x ^ l ^ Nat.card φ.ker := by
  obtain ⟨h1, m', h2⟩ := lift_spec hs t (Nat.card φ.ker)
  exact indep (h1.trans hx.symm) h2 hm

theorem del_mem (t : Tate l N) : del hs t ∈ lker φ l := by
  obtain ⟨h1, m, h2⟩ := lift_spec hs t (Nat.card φ.ker)
  refine ⟨by rw [del, map_pow, h1, t.lev_pow], m, ?_⟩
  rw [del, ← pow_mul, mul_comm, pow_mul, h2, one_pow]

def delta : Tate l N →+ Additive (lker φ l) where
  toFun t := Additive.ofMul ⟨del hs t, del_mem hs t⟩
  map_zero' := by
    show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
    congr 1
    exact Subtype.ext ((del_eq hs 0 (x := 1) (m := 0) (by rw [map_one, Tate.lev_zero]) (one_pow _)).trans
      (one_pow _))
  map_add' s t := by
    show Additive.ofMul _ = Additive.ofMul (_ * _)
    congr 1
    apply Subtype.ext
    obtain ⟨hs1, m, hs2⟩ := lift_spec hs s (Nat.card φ.ker)
    obtain ⟨ht1, m', ht2⟩ := lift_spec hs t (Nat.card φ.ker)
    refine (del_eq hs (s + t) (x := lift hs s _ * lift hs t _) (m := m + m')
      (by rw [map_mul, hs1, ht1, Tate.lev_add]) ?_).trans ?_
    · rw [mul_pow, pow_pow_eq_one hs2, add_comm, pow_pow_eq_one ht2, _root_.one_mul]
    · rw [mul_pow]; rfl

theorem delta_surjective (hd : ∀ x : M, ∃ y, y ^ l = x) : Function.Surjective (delta (l := l) hs) := by
  intro k0
  set a := Nat.card φ.ker
  obtain ⟨⟨k, hk1, m, hm⟩, rfl⟩ : ∃ z : lker φ l, Additive.ofMul z = k0 := ⟨Additive.toMul k0, rfl⟩
  obtain ⟨s, hsa⟩ := GlobalTheory.Published.tate_lev_surj l M hd a k (kill hk1 hm)
  let t : Tate l N := Tate.mk (fun n => φ (s.lev (n + a))) fun n =>
    ⟨by rw [← map_pow, add_comm, s.lev_add_pow, hsa, hk1], by rw [← map_pow, add_right_comm, s.lev_succ]⟩
  refine ⟨t, ?_⟩
  show Additive.ofMul _ = Additive.ofMul _
  congr 1
  apply Subtype.ext
  exact (del_eq hs t (x := s.lev (a + a)) (m := a + a) rfl (s.lev_pow _)).trans
    ((s.lev_add_pow a a).trans hsa)

theorem delta_ker : (delta hs).ker = (LinearMap.range (Tate.map l φ)).toAddSubgroup := by
  set a := Nat.card φ.ker
  ext t
  have e0 : t ∈ (delta hs).ker ↔ del hs t = 1 := by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val (congrArg Additive.toMul h)
    · intro h
      show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
      exact congrArg Additive.ofMul (Subtype.ext h)
  rw [e0, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · intro h
    have lv : ∀ n, (lift hs t (n + a) ^ l ^ n) ^ l ^ a = 1 := fun n => by
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + a)
      rw [← h, del_eq hs t (x := lift hs t (n + a) ^ l ^ n) (m := m)
        (by rw [map_pow, h1, add_comm, t.lev_add_pow]) (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])]
    let y : Tate l M := Tate.mk (fun n => lift hs t (n + a) ^ l ^ a) fun n => by
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul]; exact lv n, ?_⟩
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + 1 + a)
      obtain ⟨h1', m', h2'⟩ := lift_spec hs t (n + a)
      rw [← pow_mul, mul_comm, pow_mul]
      refine indep (m := m) (m' := m') ?_ (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]) h2'
      rw [map_pow, h1, h1', show n + 1 + a = (n + a) + 1 by omega, t.lev_succ]
    refine ⟨y, Tate.ext fun n => ?_⟩
    rw [Tate.lev_map, Tate.lev_mk, map_pow, (lift_spec hs t (n + a)).1, t.lev_add_pow]
  · rintro ⟨y, rfl⟩
    exact (del_eq hs _ (x := y.lev a) (m := a) rfl (y.lev_pow a)).trans (y.lev_pow a)

omit hs in
theorem map_injective' : Function.Injective (Tate.map l φ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => Tate.ext fun n => ?_
  have h1 : ∀ k, φ (y.lev k) = 1 := fun k => congrArg (·.lev k) hy
  rw [Tate.lev_zero, ← y.lev_add_pow n (Nat.card φ.ker)]
  exact kill (h1 _) (y.lev_pow _)

end GlobalTheory.TateCoker

namespace GlobalTheory

open GlobalTheory.TateCoker in

theorem tate_map_coker_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  intro l _ M N _ _ φ hd hs hf
  refine ⟨map_injective', ?_⟩
  have e1 : (Tate l N ⧸ LinearMap.range (Tate.map l φ)) ≃
      (Tate l N ⧸ (LinearMap.range (Tate.map l φ)).toAddSubgroup) := Equiv.refl _
  rw [Nat.card_congr e1, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq (delta_ker hs)).symm.toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (delta_surjective hs hd)).toEquiv]
  exact Nat.card_congr (Additive.toMul.trans (Equiv.refl _))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

noncomputable section

namespace GlobalTheory.PsiFromTauEven

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem tauCoord_mul_sq (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (D : DegPre A) (hB : D.TauBimult)
    (hE : D.PsiEven) (y : D.X) (r : A) (hr : PsiCoord D y r) (x : (FractionRing A)ˣ) (hx : IsTauCoord D y (-y) x) :
    ∃ w : Aˣ, (x : FractionRing A) * algebraMap A (FractionRing A) r ^ 2 = algebraMap A (FractionRing A) w := by
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient A D y (-y) x _ _ _ hx h0 hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit A D hE y _ _ hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := GlobalTheory.MonoTriv.psiCoord_zero D hB _ (psiCoord_spec D 0)
  refine ⟨u₂ * u₄ * u₃⁻¹, ?_⟩
  have hne : (x₀ : FractionRing A) ≠ 0 := x₀.ne_zero
  have h3 : algebraMap A (FractionRing A) (u₃ : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 u₃.ne_zero
  rw [hu₂, hu₃, hu₄, ← e₀]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsDiscreteValuationRing V → ∀ (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (D : DegPre R) (D' : DegPre V), D.TauBimult → D.PsiEven → D'.TauBimult → D'.PsiEven → ∀ ρ : D.X →+ D'.X,
    (∀ (a b : D.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' (ρ a) (ρ b) x' →
      ∃ u : Vˣ, gK (x : FractionRing R) = algebraMap V (FractionRing V) (u : V) * (x' : FractionRing V)) →
    ∀ (y : D.X) (r : R) (r' : V), PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r' := by
  intro R _ _ _ V _ _ _ hV g gK hgK D D' hB hE hB' hE' ρ hρ y r r' hr hr'
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D y (-y)
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D' (ρ y) (-(ρ y))
  obtain ⟨w, hw⟩ := tauCoord_mul_sq R D hB hE y r hr x hx
  obtain ⟨w', hw'⟩ := tauCoord_mul_sq V D' hB' hE' (ρ y) r' hr' x' hx'
  have hx'' : IsTauCoord D' (ρ y) (ρ (-y)) x' := by rwa [map_neg]
  obtain ⟨u, hu⟩ := hρ y (-y) x x' hx hx''
  have e := congrArg gK hw
  rw [map_mul, map_pow, hgK, hgK, hu] at e
  let v : Vˣ := u * w' * (Units.map g.toMonoidHom w)⁻¹
  have key : (g r) ^ 2 * (v : V) = r' ^ 2 := by
    have k1 : ((u : V) * w') * (g r) ^ 2 = g w * r' ^ 2 := by
      apply IsFractionRing.injective V (FractionRing V)
      simp only [map_mul, map_pow]
      rw [← hw', ← e]; ring
    have hw1 : (g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ) = 1 := by
      have h : ((Units.map g.toMonoidHom w : Vˣ) : V) = g w := rfl
      rw [← h, Units.mul_inv]
    simp only [v, Units.val_mul]
    calc g r ^ 2 * (↑u * ↑w' * ↑(Units.map g.toMonoidHom w)⁻¹)
        = (↑u * ↑w') * g r ^ 2 * ↑(Units.map g.toMonoidHom w)⁻¹ := by ring
      _ = r' ^ 2 * ((g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ)) := by rw [k1]; ring
      _ = r' ^ 2 := by rw [hw1, _root_.mul_one]
  have hsq : Associated ((g r) ^ 2) (r' ^ 2) := ⟨v, key⟩
  haveI : IsIntegrallyClosed V := inferInstance
  exact associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
    ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)

end GlobalTheory.PsiFromTauEven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  first | exact @GlobalTheory.TInj.PerUnit.monomial_ratio_unit | exact GlobalTheory.TInj.PerUnit.monomial_ratio_unit | (intros; apply GlobalTheory.TInj.PerUnit.monomial_ratio_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagUniversal
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB GlobalTheory.FlagZ

namespace GlobalTheory.FlagZ

theorem exists_classifying : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    ∃ g' : T ⟶ GlobalTheory.FlagZ.Fl ι N, ∃ w : g' ≫ GlobalTheory.FlagZ.flStr ι N = g, ∀ a i,
      ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g' (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w).hom.app (GlobalTheory.FlagZ.Taut.stdE N) := by
  intro ι _ N fl hfl T g fl'
  choose V hxV hV G hG using fun t : T => GlobalTheory.T.flag_locally_adapted_affine_frame g fl' t
  have hU : ⨆ t, V t = ⊤ := top_le_iff.1 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨t, hxV t⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.T.scheme_morphisms_glue_open_cover V hU
    (fun t => (hV t).isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (G t))
    fun k l => GlobalTheory.T.adapted_frames_agree_on_overlap g fl' (V k) (V l) (hV k) (hV l) (G k) (G l) (hG k) (hG l)
  have w : g' ≫ flStr ι N = g := toZ_ext _ _
  refine ⟨g', w, fun a i => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.modules_iso_of_matching_frames ((Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)) ((fl' a).ι i) i fun x => by
    obtain ⟨s₁, hs₁, e₁⟩ := GlobalTheory.T.flag_point_tautological_frame ι N fl hfl T g g' w (V x) (hV x) (G x) (hg' x) a i
    obtain ⟨s₂, hs₂, e₂⟩ := hG x a i
    exact ⟨V x, s₁, s₂, hxV x, hs₁, hs₂, fun j => (e₁ j).trans (e₂ j).symm⟩
  exact ⟨e, he⟩

end GlobalTheory.FlagZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupAction_compat_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.isActOf_of_fibreIso | exact GlobalTheory.ThetaMove.isActOf_of_fibreIso | (intros; apply GlobalTheory.ThetaMove.isActOf_of_fibreIso <;> assumption)
end

