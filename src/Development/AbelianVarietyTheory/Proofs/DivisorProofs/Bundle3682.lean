import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3680
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.TjExists

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem charZero_of_base (b : Base D R) (hp : IsUnit ((p : ℕ) : R)) {k : Type} [Field k] (s : Sp k ⟶ Sp R) :
    CharZero k := by
  let β : R →+* k := (Spec.preimage s).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hu : IsUnit ((ringChar k : ℕ) : R) := by
      by_cases h : ringChar k = p
      · rw [h]; exact hp
      · exact b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)
    have := hu.map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

attribute [local instance] ptModuleWvs

def torsSub {s : S ⟶ Sp R} (o : Obj b N s) (T : Over S) (c : ℕ) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ^ c = 1}
  zero_mem' := one_pow c
  add_mem' {g h} hg hh := by
    show (g.toMul * h.toMul) ^ c = 1
    rw [mul_pow, show g.toMul ^ c = 1 from hg, show h.toMul ^ c = 1 from hh, _root_.mul_one]
  smul_mem' a g hg := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ c = 1
    rw [← MonObj.pow_comp, show g.toMul ^ c = 1 from hg, MonObj.one_comp]

theorem comp_act_natCast {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (q : T ⟶ o.A) (n : ℕ) :
    q ≫ o.act.act (n : D.O) = q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_eq_one_wvs, pow_zero, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem exists_sub (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hj : j ≤ D.n)
    (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {s : Sp k ⟶ Sp R} (o : Obj b N s) :
    ∃ H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A), (∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) ∧ (∀ h ∈ H, h ^ c = 1) ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift h₁ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h₂) 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H) ∧
      (∀ h ∈ H, (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) → KilledBy o w h) ∧
      Nat.card {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} = Ideal.absNorm w ^ j := by
  obtain ⟨ex, hce, hje⟩ := hc
  have hpk : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hck : (c : k) ≠ 0 := by rw [hce, Nat.cast_pow]; exact pow_ne_zero _ hpk
  obtain ⟨e, he, hl, hr, hadj, hskew, hnd⟩ : ∃ e : (𝟙_ (Over (Sp k)) ⟶ o.A) → (𝟙_ (Over (Sp k)) ⟶ o.A) → kˣ,
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 →
        e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 →
        e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : 𝟙_ (Over (Sp k)) ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) :=
    PQuot.exists_pairing o c ⟨ex, hce⟩ k hpk (𝟙 _)
  have hinj : Function.Injective (unitOn (R := k)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hone : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
  have he1 : ∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      (Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') 1 ↔
        e g g' = 1) := fun g g' hg hg' => by
    rw [he g g' hg hg']
    exact ⟨fun h => (hinj (hone.trans h)).symm, fun h => by rw [h]; exact hone.symm⟩
  let M := torsSub o (𝟙_ (Over (Sp k))) c
  haveI : Finite M := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
  have hM0 : ∀ x : M, x = 0 ↔ x.1.toMul = 1 := fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (x : M), (∀ a ∈ v, a • x = 0) ↔ KilledBy o v x.1.toMul :=
    fun v x => forall₂_congr fun a _ => hM0 (a • x)
  have hwne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  have hq : 0 < Ideal.absNorm w := Nat.pos_of_ne_zero fun h => hwne (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero]
      haveI : Nonempty {x : M // ∀ a ∈ w, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
      exact Nat.card_pos
    · have hrk : Nat.card {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) :=
        GlobalTheory.T.card_torsion_killed_by_ideal_char_zero p D R b N (Sp k) s o w hwne k (𝟙 _)
      have htor : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, KilledBy o w g → g ^ c = 1 := fun g hg => by
        have h1 := hg _ (hu (p_mem_uIdeal D r))
        rw [map_natCast, comp_act_natCast] at h1
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hje hj0).ne'
        rw [hce, pow_succ', pow_mul, h1, one_pow]
      let φ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} ≃ {x : M // ∀ a ∈ w, a • x = 0} :=
        { toFun := fun g => ⟨⟨Additive.ofMul g.1, htor g.1 g.2⟩, (hkill w _).2 g.2⟩
          invFun := fun x => ⟨x.1.1.toMul, (hkill w _).1 x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_congr φ, hrk, hm, Nat.one_mul]
      exact Nat.pow_le_pow_right hq hj
  obtain ⟨K, Kiso, Kmax, Ku, Kcard⟩ := GlobalTheory.T.perfect_pairing_torsion_module p D r w j c hw hu ⟨ex, hce⟩ M
    (fun x => (hM0 _).2 x.2) k (fun x y => e x.1.toMul y.1.toMul)
    (fun x x' y => hl _ _ _ x.2 x'.2 y.2) (fun x y y' => hr _ _ _ x.2 y.2 y'.2)
    (fun a x y => by
      have := hadj (algebraMap (𝓞 D.F) D.O a) _ _ x.2 y.2
      rw [D.star_F, MulOpposite.unop_op] at this
      exact this)
    (fun x y => hskew _ _ x.2 y.2)
    (fun x h => (hM0 x).2 (hnd _ x.2 fun g' hg' => h ⟨Additive.ofMul g', hg'⟩)) hle
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A) :=
    { carrier := {g | ∃ x ∈ K, x.1.toMul = g}
      one_mem' := ⟨0, K.zero_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, rfl⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, K.neg_mem hx, rfl⟩ }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c' _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.T.integers_surjective_of_rank_one p D hm c'
    exact ⟨a • x, K.smul_mem a hx, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he1 _ _ x.2 y.2).2 (Kiso x hx y hy)
  · intro g hg h
    exact ⟨⟨Additive.ofMul g, hg⟩, Kmax _ fun y hy => (he1 _ _ hg y.2).1 (h _ ⟨y, hy, rfl⟩), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨i, hi⟩
    exact (hkill w x).1 (Ku x hx ⟨i, (hkill _ x).2 hi⟩)
  · rw [← Kcard]
    refine (Nat.card_eq_of_bijective (fun x : {x : M // x ∈ K ∧ ∀ a ∈ w, a • x = 0} =>
      (⟨x.1.1.toMul, ⟨x.1, x.2.1, rfl⟩, (hkill w _).1 x.2.2⟩ :
        {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h})) ⟨fun x y h => ?_, ?_⟩).symm
    · exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
    · rintro ⟨_, ⟨x, hx, rfl⟩, hk⟩
      exact ⟨⟨x, hx, (hkill w x).2 hk⟩, rfl⟩

theorem exists_isPIsog_isTj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : Obj b N s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ := by
  intro p _ D R _ _ b N _ _ hp r w j c hw hu hj hc hm k _ _ s o
  haveI := charZero_of_base b hp s
  obtain ⟨H, stab, hpow, hiso, hmax, hU, hcard⟩ := exists_sub r w j c hw hu hj hc hm o
  obtain ⟨ex, hce, -⟩ := hc
  have hck : (c : k) ≠ 0 := by
    rw [hce, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin : Finite H := by
    haveI := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
    exact Finite.of_injective (fun h : H => (⟨h.1, hpow h.1 h.2⟩ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // g ^ c = 1}))
      fun a a' h => Subtype.ext (Subtype.mk.inj h)
  have hinj : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h h' : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = toUnit (Over.mk x) ≫ h' → h = h' := fun κ _ x h h' e => by
    haveI : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum κ))
    haveI := GlobalTheory.PointQuot.epi_toUnit (Over.mk x)
    exact (cancel_epi _).1 e
  have hfree : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = 1 ↔ h = 1 := fun κ _ x h =>
    ⟨fun e => hinj κ x h 1 (by rw [e, MonObj.comp_one]), fun e => by rw [e, MonObj.comp_one]⟩
  obtain ⟨o', ψ, hψ, hker⟩ := PQuot.exists_quot o c ⟨ex, hce⟩ hp H hfin (fun κ _ _ x h _ e => (hfree κ x h).1 e)
    stab hpow hiso (fun κ _ _ x g hg ho => PQuot.max_geom o c hck H hpow hmax κ x g hg ho)
  refine ⟨o', ψ, hψ, fun κ _ _ _ x => ?_⟩
  have hkb : ∀ (v : Ideal (𝓞 D.F)) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      KilledBy o v (toUnit (Over.mk x) ≫ h) ↔ KilledBy o v h := fun v h =>
    forall₂_congr fun a _ => by rw [Category.assoc, hfree]
  refine ⟨fun g hg ⟨i, hi⟩ => ?_, ?_⟩
  · obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
    exact (hkb w h).2 (hU h hh ⟨i, (hkb _ h).1 hi⟩)
  · rw [hm, Nat.one_mul, ← hcard]
    refine (Nat.card_eq_of_bijective (fun h : {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} =>
      (⟨toUnit (Over.mk x) ≫ h.1, (hker κ x _).2 ⟨h.1, h.2.1, rfl⟩, (hkb w _).2 h.2.2⟩ :
        {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g})) ⟨fun a a' h => ?_, ?_⟩).symm
    · exact Subtype.ext (hinj κ x _ _ (congrArg Subtype.val h))
    · rintro ⟨g, hg, hk⟩
      obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
      exact ⟨⟨h, hh, (hkb w h).1 hk⟩, rfl⟩

end GlobalTheory.UPel.HT.ES.TjExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundary
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

def constEps {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k)) :
    MvPowerSeries σ k →+* DualNumber k where
  toFun r := TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Derivation.leibniz, mul_comm, add_comm]

theorem constEps_apply {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k))
    (r : MvPowerSeries σ k) :
    constEps δ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) +
      TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r)) := rfl

theorem residue_eq_zero_iff_constantCoeff {σ k : Type} [Field k] (r : MvPowerSeries σ k) :
    residue _ r = 0 ↔ MvPowerSeries.constantCoeff r = 0 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

theorem logKS_inj_mod_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x, x ∉ interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hvb hA D Θ m hm hx hKS hΘ
  obtain ⟨x, hxi, hxU, hxm⟩ := hx
  have h2 := GlobalTheory.T.exists_closedBoundaryPoint_maximalIdeal E H Dw l Xo c Y hsm U m hm x hxi hxU hxm
  obtain ⟨x', hx'x, hx'bd, hx'cl⟩ := h2
  have h3 := hrig x' hx'bd hx'cl
  obtain ⟨k, _, m', d, ξ, t, P, gam, hξ, hEt, hId, hBd, hSAB, hMon, hPart, hRig⟩ := h3
  have hxU' : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := by
    show genι Y (ξ (closedPoint _)) ∈ U.1
    rw [hξ, hx'x]
    exact hxU
  have hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1 := top_le_preimage_of_closedPoint _ _ hxU'
  have h4 := GlobalTheory.ChartDer.logDer_extend_chartRing E H Dw l Xo c Y U D k m' d ξ hxU' hEt hId
  obtain ⟨DR, hDR0, hDRt⟩ := h4
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = ((Scheme.stalkClosedPointTo ξ).hom.comp
      (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hxU').hom.comp ((genι Y).app U.1).hom)) r := by
    intro r
    have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq ξ (genι Y ⁻¹ᵁ U.1) hxU'
    have e2 := congrArg (fun φ => φ.hom (((genι Y).app U.1).hom r)) e
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [RingHom.comp_apply, RingHom.comp_apply, e2, valR, dif_pos hU, Scheme.Hom.comp_appLE]
    rfl
  have hDR : ∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r) := by
    intro r
    rw [hval, hval]
    exact hDR0 r
  have ha' : ∀ i, ∃ a, DR (bdParam k m' d i) = a * bdParam k m' d i := fun i => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hDRt i)
    exact ⟨a, ha.symm⟩
  choose a ha using ha'
  have hc := GlobalTheory.T.degeneration_constant_of_logKodairaSpencer_mem E H Dw l Xo c Y hpq hsm hsnc U n v A hv hvb hA D Θ m hm x hxi hxU hxm hKS hΘ k m' d ξ x' hξ
    hx'x t P gam hEt hId hBd hSAB hMon hPart hU DR a hDR ha (constEps DR) (constEps_apply DR)
  obtain ⟨c₀, hc₀, hcc⟩ := hc
  have ht0 : ∀ i, MvPowerSeries.constantCoeff (bdParam k m' d i) = 0 := fun i => by simp
  have hsnd : ∀ r, (constEps DR r).snd = 0 := by
    have h1 : ∀ r ∈ maximalIdeal (ChartRing k m' d), (constEps DR r).fst = 0 := fun r hr => by
      rw [constEps_apply]
      simpa using (residue_eq_zero_iff_constantCoeff r).1 ((residue_eq_zero_iff r).2 hr)
    have h2 : ∀ i, constEps DR (bdParam k m' d i) = 0 := fun i => by
      rw [constEps_apply, ha i, map_mul, ht0 i, mul_zero]
      simp
    exact hRig k (constEps DR) _ h1 h2 hcc
  have hres : ∀ r, residue _ (DR r) = 0 := fun r => by
    rw [residue_eq_zero_iff_constantCoeff]
    simpa [constEps_apply] using hsnd r
  haveI : CharZero k := by
    let f : c.F →+* k := MvPowerSeries.constantCoeff.comp (Spec.preimage (ξ ≫ genι Y ≫ Y.s)).hom
    exact charZero_of_injective_ringHom f.injective
  have hli : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (levelForms H l.M' P.D.toPre.X).subtype (Submodule.ker_subtype _)
  have hdir := GlobalTheory.ConstPointCone.dir_eq_zero_of_const (ChartRing k m' d) P.D.toPre m' (bdParam k m' d)
    (fun i => gam i) hMon hli (fun i => by simp [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff])
    (fun i y z => (gam i).2.1 y z) k (constEps DR) _ hsnd hcc
  have ha0 : ∀ i, residue _ (a i) = 0 := fun i => by
    rw [residue_eq_zero_iff_constantCoeff]
    have := congrFun hdir i
    simp only [Pi.zero_apply, mul_eq_zero, Rat.cast_eq_zero, hc₀, false_or] at this
    exact this
  exact GlobalTheory.T.logVectorField_mem_maxIdeal_smul_of_vanishing E H Dw l Xo c Y hsm hsnc U D m hm x hxi hxU hxm k m' d ξ x' hξ hx'x hEt hId hBd hU DR a hDR ha
    hres ha0

end GlobalTheory.ChartDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOnStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unif_pullback_of_canonical_on : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.TChart.Taut.unif_pull_of_canonOn | exact GlobalTheory.TChart.Taut.unif_pull_of_canonOn | (intros; apply GlobalTheory.TChart.Taut.unif_pull_of_canonOn <;> assumption)
end

