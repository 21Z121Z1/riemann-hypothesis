import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SpecialCount

theorem transfer {M N : Type} [CommGroup M] [Group N] (H : Subgroup M) (r : H →* N) (Φ : MulAut M)
    (φ : ℕ → N → N) (hφ : ∀ (j : ℕ) (x : H), ∃ h : Φ^[j] x ∈ H, r ⟨_, h⟩ = φ j (r x)) (l e : ℕ)
    (hinj : ∀ n (x : H), x ^ l ^ n = 1 → r x = 1 → x = 1) (V : Subgroup N)
    (hV : ∀ x ∈ V, φ 1 x = x ^ e) (hfin : ∀ n, Finite {x : N // x ^ l ^ n = 1}) (Q : Polynomial ℤ)
    (hQ : ∀ (x : N) n, x ^ l ^ n = 1 →
      ((List.range (Q.natDegree + 1)).map fun j => φ j x ^ Q.coeff j).prod ∈ V) :
    ∃ U : Subgroup M,
      (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ Nat.card {x : N // x ^ l ^ n = 1} ∧
        Nat.card {x : U // x ^ l ^ n = 1} ≤ Nat.card {x : V // x ^ l ^ n = 1}) ∧
      (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → Φ x = x ^ e) ∧
      ∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), (Φ^[j] x) ^ Q.coeff j ∈ U := by
  have inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y := by
    intro n x y hx hy h
    have := hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.1 this
  have memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩
  · have := hfin n
    refine Nat.card_le_card_of_injective
      (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))
  · have := hfin n
    have : Finite {x : V // x ^ l ^ n = 1} :=
      Finite.of_injective (β := {x : N // x ^ l ^ n = 1})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h =>
          Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))
    have tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1},
        (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1 := fun x =>
      Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by
        change r _ ^ l ^ n = 1
        rw [← map_pow, tor x, map_one])⟩) fun x y h => ?_
    have := inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)
    exact Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))
  · obtain ⟨h, hv⟩ := (memU x).1 hx
    obtain ⟨h', e'⟩ := hφ 1 ⟨x, h⟩
    have := inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by
        change Φ x ^ l ^ n = 1
        rw [← map_pow, hn, map_one])) (Subtype.ext (by
        change (x ^ e) ^ l ^ n = 1
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])
    exact congrArg Subtype.val this
  · choose h e' using fun j => hφ j ⟨x, hx⟩
    have hr := hQ (r ⟨x, hx⟩) n (by
      rw [← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])
    refine ⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩
    · change r _ ∈ V
      rw [map_list_prod, List.map_map]
      have : (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j := by
        funext j
        simp only [Function.comp, map_zpow, e']
      rw [this]
      exact hr
    · rw [map_list_prod, List.map_map]
      rfl

theorem exists_restrict {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hi : Function.Injective (algebraMap R Ω)) (q : ℕ) (ψ : Ω →+* Ω)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) :
    ∃ σ : R →+* R, (∀ x, algebraMap R Ω (σ x) = ψ (algebraMap R Ω x)) ∧
      ∀ x, IsLocalRing.residue R (σ x) = IsLocalRing.residue R x ^ q := by
  choose f hf hf' using h
  refine ⟨{ toFun := f
            map_one' := hi (by simp [hf])
            map_mul' := fun x y => hi (by simp [hf])
            map_zero' := hi (by simp [hf])
            map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 (hf' x)
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem smConn_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (h : SmConn G) :
    SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd _ _); infer_instance
  · show IsSeparated (pullback.snd _ _); infer_instance
  · show QuasiCompact (pullback.snd _ _); infer_instance
  · show GeometricallyConnected (pullback.snd _ _); infer_instance

end GlobalTheory.SS.SpecialCount

namespace GlobalTheory.SS
open SpecialCount

theorem frobenius_on_integral_torsion : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσ'⟩ := exists_restrict hi (p ^ r) ψ hψR
  have hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w := fun w => hi (by
    rw [hσ, ← IsScalarTower.algebraMap_apply, hψW])
  obtain ⟨F, hF, hFx⟩ := GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by
      rw [RingHom.comp_apply, ← hσ', hσW]) hfin G hG
  have hlp : l ≠ p := by
    rintro rfl
    have := hlu.map (IsLocalRing.residue R)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this
  have hq : 2 ≤ p ^ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩ := GlobalTheory.T.frobenius_on_torsion_alt _ p l hl hlp _
    (smConn_pullback _ G hG) g (by
      show SmoothOfRelativeDimension g (pullback.snd _ _)
      exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF
  obtain ⟨H₀, red, hH, hred, hinj⟩ := GlobalTheory.RedPts.exists_reduction W R Ω hi G hG
  let H : Subgroup M := H₀.comap θ.toMonoidHom
  let κ : H →* H₀ := (θ.toMonoidHom.subgroupComap H₀)
  have step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F) := by
    intro x
    obtain ⟨s, hs, hs'⟩ := (hH _).1 x.2
    have a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R) := by
      rw [Category.assoc, hs, sp_comp]
      congr 1
      exact RingHom.ext hσW
    have a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left := by
      rw [hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from
        RingHom.ext hσ, ← sp_comp, Category.assoc, hs']
      rfl
    have hx : Ψ x ∈ H := (hH _).2 ⟨_, a1, a2⟩
    refine ⟨hx, ?_⟩
    have b1 := hred (κ ⟨_, hx⟩) _ a1 a2
    have b2 := hred (κ x) s hs hs'
    have b3 := hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)
    ext1
    apply pullback.hom_ext
    · refine b1.trans (Eq.trans ?_ b3.symm)
      erw [b2]
      rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
      congr 2
      exact RingHom.ext hσ'
    · exact (Over.w _).trans (Over.w _).symm
  have iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H,
      red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F ^ n) := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩
    | succ n ih =>
      intro x
      obtain ⟨h, e⟩ := step x
      obtain ⟨h', e'⟩ := ih ⟨_, h⟩
      rw [pow_succ, pow_succ]
      refine ⟨h', e'.trans ?_⟩
      rw [e, Category.assoc]
      rfl
  obtain ⟨U, hU1, hU2, hU3⟩ := transfer H (red.comp κ) (Ψ ^ m)
    (fun j x => x ≫ (show _ ⟶ _ from (F ^ m) ^ j)) (fun j x => by
      have e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x := by
        rw [pow_mul]
        generalize (x : M) = y
        induction j generalizing y with
        | zero => rfl
        | succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]; rfl
      rw [e, ← pow_mul]
      exact iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by
      have := hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n)
        (by rw [← map_pow, hx, map_one]) h
      exact Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V
    (fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ
  refine ⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1,
    (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩
  rw [Nat.cast_pow]
  exact hroot β hβ

end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionOfSurjectiveOfDimEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace IsogenyOntoExtension

theorem exists_pow_eq_one_of_finite_kernel {k : Type} [Field k] {G B : Over (Sp k)} [GrpObj G]
    [GrpObj B] [IsCommMonObj G] (f : G ⟶ B) [IsMonHom f]
    (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → x ^ n = 1 := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hm : Mono i := ⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩
  have hi : i ≫ f = 1 := hp.w
  obtain ⟨gZ, hZ⟩ := exists_grpObj_of_mono i (hp.lift η[G] (toUnit _) (by simp))
    (hp.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one,
        _root_.mul_one, Hom.one_def]))
    (hp.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hp.lift_fst _ _ _) (by rw [hp.lift_fst, Hom.mul_def]; congr 1)
    (by rw [hp.lift_fst, Hom.inv_def])
  have hZf : IsFinite Z.hom := by simpa using hf
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main k Z hZf inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hp.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

open RationalPoint in

theorem finite_kernel_points {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)}
    [GrpObj B] (f : G ⟶ B) (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    {x : 𝟙_ (Over (Sp k)) ⟶ G | x ≫ f = 1}.Finite := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hZf : IsFinite Z.hom := by simpa using hf
  have h1 : Finite Z.left := by
    have := Z.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    exact this.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have h2 : Finite (𝟙_ (Over (Sp k)) ⟶ Z) := Finite.of_injective _ pt_injective
  refine (Set.finite_range fun z : 𝟙_ (Over (Sp k)) ⟶ Z => z ≫ i).subset fun x hx => ?_
  exact ⟨hp.lift x (toUnit _) hx, hp.lift_fst _ _ _⟩

open RationalPoint in

theorem eq_top_of_finite_cover {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left]
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) {Z : Set G.left} (hZ : IsClosed Z)
    (hH : ∀ x, x ∈ H ↔ pt x ∈ Z) {F : Set (𝟙_ (Over (Sp k)) ⟶ G)} (hF : F.Finite)
    (hc : ∀ y, ∃ a ∈ F, a * y ∈ H) : H = ⊤ := by
  classical
  let t : (𝟙_ (Over (Sp k)) ⟶ G) → (G ⟶ G) := fun a => (toUnit G ≫ a) * 𝟙 G
  have ht : ∀ a y : 𝟙_ (Over (Sp k)) ⟶ G, y ≫ t a = a * y := fun a y => by
    simp only [t]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp,
      Category.comp_id]
  let C : (𝟙_ (Over (Sp k)) ⟶ G) → Set G.left := fun a => (t a).left ⁻¹' Z
  have hC : ∀ a, IsClosed (C a) := fun a => hZ.preimage (t a).left.continuous
  have hCm : ∀ a y, pt y ∈ C a ↔ a * y ∈ H := fun a y => by
    rw [hH, ← ht, pt_comp]; rfl
  have hU : IsClosed (⋃ a ∈ F, C a) := hF.isClosed_biUnion fun a _ => hC a
  have hcov : (Set.univ : Set G.left) ⊆ ⋃ a ∈ F, C a := by
    by_contra hne
    have hne' : (⋃ a ∈ F, C a)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (h ▸ subset_rfl)
    have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
    obtain ⟨c, hcZ, hc'⟩ := nonempty_inter_closedPoints hne' hU.isOpen_compl.isLocallyClosed
    obtain ⟨x, hx⟩ := exists_pt_mem (X := G) (Z := {c}) hc' ⟨c, rfl⟩
    obtain ⟨a, ha, hax⟩ := hc x
    refine hcZ ?_
    rw [← show pt x = c from hx]
    exact Set.mem_biUnion ha ((hCm a x).2 hax)
  obtain ⟨D, hD, hDu⟩ := (isIrreducible_iff_sUnion_isClosed.1
    (IrreducibleSpace.isIrreducible_univ G.left)) (hF.image C).toFinset (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hz
      exact hC a) (by rwa [Set.Finite.coe_toFinset, Set.sUnion_image])
  obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hD
  rw [eq_top_iff]
  intro y _
  have := (hCm a (a⁻¹ * y)).1 (hDu trivial)
  rwa [mul_inv_cancel_left] at this

end IsogenyOntoExtension

open IsogenyOntoExtension RationalPoint in

theorem torusExtension_of_surjective_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → Nonempty (TorusExtension G') → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Nonempty (TorusExtension G) := by
  intro k _ _ G G' _ _ g hG hG' hg hg' hT i hi hs
  have hker := GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension k G G' g hG hG' hg hg' i hi hs
  obtain ⟨hfl, hsu⟩ := GlobalTheory.T.flat_and_surjective_of_surjective_points' k G G' hG hG' i hi hs
  obtain ⟨c, s, p, q, n⟩ := id hG
  obtain ⟨c', s', p', q', n'⟩ := id hG'
  obtain ⟨N, hN, hkill⟩ := exists_pow_eq_one_of_finite_kernel i hker
  have hqc : QuasiCompact i.left := by
    have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp i.left G'.hom
  have hmul : IsMonHom (𝟙 G ^ N) := by
    clear hkill hN
    induction N with
    | zero => rw [pow_zero]; exact Serre.isMonHom_one
    | succ m ih => rw [pow_succ]; exact Serre.isMonHom_mul _ _
  obtain ⟨⟨r, hr, hir⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ G G' G i (𝟙 G ^ N) hi hmul
    hfl hsu hqc fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hkill T x hx]
  refine GlobalTheory.T.nonempty_torusExtension_of_surjective_points' k G' G hG hT r hr ?_
  obtain ⟨Z, hZ, hZm⟩ := exists_isClosed_image_of_isClosed_subgroup k G' G r hr inferInstance q'
    inferInstance q ⊤ Set.univ isClosed_univ (by simp)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G') →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ r) fun x y => MonObj.mul_comp x y r
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have htop : φ.range = ⊤ := by
    refine eq_top_of_finite_cover φ.range hZ (fun x => ?_) (finite_kernel_points i hker) fun y => ?_
    · rw [← range_left_subset_iff, ← hZm]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, trivial, ha⟩, fun ⟨a, _, ha⟩ => ⟨a, ha⟩⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.T.torusExtension_points_divisible' k G' hT N hN (y ≫ i)
      obtain ⟨x, rfl⟩ := hs z
      refine ⟨x ^ N * y⁻¹, ?_, x ≫ i, ?_⟩
      · show _ ≫ i = 1
        rw [MonObj.mul_comp, GrpObj.inv_comp, MonObj.pow_comp, hz, mul_inv_cancel]
      · show (x ≫ i) ≫ r = _
        rw [Category.assoc, hir, MonObj.comp_pow, Category.comp_id, inv_mul_cancel_right]
  intro y
  exact (htop ▸ Subgroup.mem_top y : y ∈ φ.range)

end GlobalTheory
end

