import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionOnChart
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionOnChart

def zloc (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by simp [neg_div]⟩
  mul_mem' := by
    rintro x z ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro x z ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hb hb', ?_⟩
    have h0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    have h0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb' (h ▸ dvd_zero p)
    push_cast
    rw [div_add_div _ _ h0 h0']

theorem zloc_range (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zloc Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) :=
  ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem overring {R₀ R Ω : Type} [CommRing R₀] [IsDomain R₀] [CommRing R] [IsDomain R] [Field Ω]
    [Algebra R₀ Ω] [Algebra R Ω] [IsIntegrallyClosed R₀] [IsFractionRing R₀ Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (hle : ∀ x : R₀, ∃ r : R, algebraMap R Ω r = algebraMap R₀ Ω x)
    (hden : ∀ r : R, ∃ (s x : R₀) (u : R), algebraMap R₀ Ω s * algebraMap R Ω u = 1 ∧
      algebraMap R Ω r * algebraMap R₀ Ω s = algebraMap R₀ Ω x) :
    IsIntegrallyClosed R ∧ IsFractionRing R Ω := by
  choose φ hφ using hle
  let f : R₀ →+* R :=
    { toFun := φ
      map_one' := hinj (by rw [hφ, map_one, map_one])
      map_zero' := hinj (by rw [hφ, map_zero, map_zero])
      map_mul' := fun a b => hinj (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_add' := fun a b => hinj (by rw [hφ, map_add, map_add, hφ, hφ]) }
  have hf : ∀ x, algebraMap R Ω (f x) = algebraMap R₀ Ω x := hφ
  clear_value f
  have hfi : Function.Injective f := fun a b h => IsFractionRing.injective R₀ Ω (by rw [← hf, ← hf, h])
  let M : Submonoid R₀ := (IsUnit.submonoid R).comap f
  have hM : M ≤ nonZeroDivisors R₀ := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h => by
      have hu : IsUnit (f s) := hs
      rw [h, map_zero] at hu
      exact not_isUnit_zero hu
  letI : Algebra R₀ R := f.toAlgebra
  have hloc : IsLocalization M R := by
    refine (isLocalization_iff _ _).2 ⟨fun s => s.2, fun z => ?_, fun {x z} h => ⟨1, by rw [hfi h]⟩⟩
    obtain ⟨s, x, u, hu, hx⟩ := hden z
    have hs : IsUnit (f s) := IsUnit.of_mul_eq_one u (hinj (by rw [map_mul, hf, hu, map_one]))
    refine ⟨(x, ⟨s, hs⟩), hinj ?_⟩
    change algebraMap R Ω (z * f s) = algebraMap R Ω (f x)
    rw [map_mul, hf, hf, hx]
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hinj
  refine ⟨isIntegrallyClosed_of_isLocalization R M hM, IsFractionRing.of_field _ _ fun ω => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R₀) ω
  exact ⟨f a, f b, by rw [hf, hf]⟩

section Loc

variable {Ω : Type} [Field Ω] {A : Type} [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime]
  (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]

include O in
theorem inv_mem_range {s : A} (hs : s ∉ m) :
    algebraMap A Ω s ≠ 0 ∧ ∃ u : O, algebraMap O Ω u = (algebraMap A Ω s)⁻¹ := by
  obtain ⟨u, hu⟩ := (IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)).exists_right_inv
  have h : algebraMap A Ω s * algebraMap O Ω u = 1 := by
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul]
    exact (congrArg _ hu).trans (map_one _)
  exact ⟨left_ne_zero_of_mul_eq_one h, u, eq_inv_of_mul_eq_one_right h⟩

theorem zloc_le [CharZero Ω] (p : ℕ) [Fact p.Prime] (hp : (p : A) ∈ m) (z : zloc Ω p) :
    ∃ u : O, algebraMap O Ω u = (z : Ω) := by
  obtain ⟨x, a, b, hb, rfl⟩ := z
  have hbm : (b : A) ∉ m := by
    intro h
    have hc : IsCoprime (p : ℤ) (b : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hb)
    obtain ⟨u, v, huv⟩ := hc
    have h1 : (u : A) * (p : A) + (v : A) * (b : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact (‹m.IsPrime›).ne_top ((Ideal.eq_top_iff_one m).2
      (h1 ▸ m.add_mem (m.mul_mem_left _ hp) (m.mul_mem_left _ h)))
  obtain ⟨-, u, hu⟩ := inv_mem_range (Ω := Ω) m O hbm
  refine ⟨(a : O) * u, ?_⟩
  rw [map_mul, hu, map_intCast, map_natCast]
  exact (div_eq_mul_inv _ _).symm

theorem le_adjoin {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (ho : ∀ z : o, ∃ u : O, algebraMap O Ω u = algebraMap o Ω z) :
    ∀ x ∈ Algebra.adjoin o T, x ∈ Algebra.adjoin O T := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht => exact Algebra.subset_adjoin ht
  | algebraMap z =>
    obtain ⟨u, hu⟩ := ho z
    rw [← hu]
    exact Subalgebra.algebraMap_mem _ u
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem exists_den {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) :
    ∀ x ∈ Algebra.adjoin O T, ∃ s : A, s ∉ m ∧ x * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht =>
    refine ⟨1, m.primeCompl.one_mem, ?_⟩
    rw [map_one, _root_.mul_one]
    exact Algebra.subset_adjoin ht
  | algebraMap z =>
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
    refine ⟨s, s.2, ?_⟩
    have h' := congrArg (algebraMap O Ω) h
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'
    rw [h']
    exact hA a
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hz⟩ := hz
    refine ⟨s * t, m.primeCompl.mul_mem hs ht, ?_⟩
    have e : (x + z) * algebraMap A Ω (s * t) =
        x * algebraMap A Ω s * algebraMap A Ω t + z * algebraMap A Ω t * algebraMap A Ω s := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem hx (hA t)) (mul_mem hz (hA s))
  | mul x z _ _ hx hz =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hz⟩ := hz
    refine ⟨s * t, m.primeCompl.mul_mem hs ht, ?_⟩
    have e : (x * z) * algebraMap A Ω (s * t) =
        x * algebraMap A Ω s * (z * algebraMap A Ω t) := by
      rw [map_mul]; ring
    rw [e]
    exact mul_mem hx hz

include m in
theorem main {o : Type} [CommRing o] [Algebra o Ω] (T : Set Ω)
    (ho : ∀ z : o, ∃ u : O, algebraMap O Ω u = algebraMap o Ω z)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T)
    (h1 : IsIntegrallyClosed (Algebra.adjoin o T)) (h2 : IsFractionRing (Algebra.adjoin o T) Ω) :
    IsIntegrallyClosed (Algebra.adjoin O T) ∧ IsFractionRing (Algebra.adjoin O T) Ω := by
  refine overring (R₀ := Algebra.adjoin o T) (R := Algebra.adjoin O T) Subtype.val_injective
    (fun x => ⟨⟨x.1, le_adjoin O T ho x.1 x.2⟩, rfl⟩) fun r => ?_
  obtain ⟨s, hs, hz⟩ := exists_den m O T hA r.1 r.2
  obtain ⟨h0, u, hu⟩ := inv_mem_range (Ω := Ω) m O hs
  refine ⟨⟨_, hA s⟩, ⟨_, hz⟩, ⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩, ?_, rfl⟩
  change algebraMap A Ω s * algebraMap O Ω u = 1
  rw [hu, mul_inv_cancel₀ h0]

end Loc

end PositivityTheory.Xgn.FunctionOnChart

theorem PositivityTheory.Xgn.exists_function_on_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hp O _ _ _ _ _ _ _ c' hc'
  haveI : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, hA, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  obtain ⟨-, -, -, -, -, -, hch⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (PositivityTheory.Xgn.FunctionOnChart.zloc Ω p) (PositivityTheory.Xgn.FunctionOnChart.zloc_range Ω p)
  obtain ⟨-, h1, h2, -⟩ := hch c' hc'
  refine ⟨?_, PositivityTheory.Xgn.FunctionOnChart.main m O (Set.range fun j => mseg y j / mseg y c')
    (PositivityTheory.Xgn.FunctionOnChart.zloc_le m O p hp) (fun a => ?_) h1 h2⟩
  · haveI : Algebra.FiniteType O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
      Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
    exact Algebra.FiniteType.isNoetherianRing O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c'))
  · have h : algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c') := hA c' hc' a
    generalize algebraMap A Ω a = x at h
    induction h using Algebra.adjoin_induction with
    | mem t ht => exact Algebra.subset_adjoin ht
    | algebraMap n => simpa using intCast_mem _ n
    | add s t _ _ hs ht => exact add_mem hs ht
    | mul s t _ _ hs ht => exact mul_mem hs ht
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceFamilyPairing
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceFamilyPairing

theorem val_mem {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R B T : Type} [Field Ω] [CommRing R] [CommRing B] [CommRing T]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : Spec (CommRingCat.of R) ⟶ X) (t : Spec (CommRingCat.of T) ⟶ X)
    (φ : R →+* Ω) (ψ : R →+* B) (k : B →+* Ω) (s : T →+* B) (g : T →+* Ω)
    (hk : k.comp ψ = φ) (hs : k.comp s = g)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (ht : Spec.map (CommRingCat.ofHom ψ) ≫ x = Spec.map (CommRingCat.ofHom s) ≫ t)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (v : epsAt t ⟶ G) (hv : IsTanAt G t v)
    (he : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) : u e ∈ k.range := by
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists X G B (Spec.map (CommRingCat.ofHom ψ) ≫ x)
  obtain ⟨L'', _, _, ⟨M''⟩⟩ := lieModel_exists X G T t
  have hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hk, hx]
  obtain ⟨β, hβ, -, hsp, hext⟩ := HTPull.lieBC ψ x _ rfl hsm M₀ M'
  obtain ⟨j', hj', hjs, -, -⟩ := HTPull.lieBC k _ ξ hξ hsm M' M
  obtain ⟨j₂, hj₂, -, -, -⟩ := HTPull.lieBC s t _ ht hsm M'' M'
  obtain ⟨u', hu'⟩ := hext u₀
  have hjj : ∀ l, j' (β l) = j₀ l := fun l => M.inj (Over.OverMorphism.ext (by
    rw [hj', hβ, hj₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hk]))
  have hall : ∀ e' : L', u (j' e') = k (u' e') := by
    intro e'
    have he' : e' ∈ Submodule.span B (Set.range β) := by rw [hsp]; trivial
    induction he' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [hjj, hu, hu', ← hk]
      rfl
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hjs, hb]
  obtain ⟨l, rfl⟩ := M''.onto v hv
  have e1 : e = j' (j₂ l) := M.inj (Over.OverMorphism.ext (by
    rw [he, hj', hj₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hs]))
  rw [e1, hall]
  exact ⟨_, rfl⟩

theorem val_frac {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R : Type} [Field Ω] [CommRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (he : e ∈ M.lat ⟨x z, hz⟩) : ∃ r s : R, s ∉ z.asIdeal ∧ φ s * u e = φ r := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hun : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hun
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hun r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : ∀ a, lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := fun a => ConcreteCategory.congr_hom e4 a
  have e6 : Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) ≫ x =
      Spec.map (CommRingCat.ofHom (x.stalkMap z).hom) ≫ X.fromSpecStalk (x z) :=
    (congrArg (· ≫ x) e0.symm).trans (Scheme.SpecMap_stalkMap_fromSpecStalk x).symm
  obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ Li M ⟨x z, hz⟩).1 e).1 he
  obtain ⟨b, hb⟩ := val_mem hsm ξ x (X.fromSpecStalk (x z)) φ
    (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z)) lam (x.stalkMap z).hom (genMap ξ ⟨x z, hz⟩)
    (RingHom.ext hlam) (RingHom.ext e5) hx e6 M₀ M j₀ hj₀ u₀ u hu e v hv hev
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl b
  refine ⟨r, s, s.2, ?_⟩
  rw [← hb, ← hlam, ← hlam, ← map_mul, mul_comm]
  exact congrArg lam hrs

theorem mem_of_frac {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (a : Ω)
    (h : ∀ z : PrimeSpectrum R, ∃ r s : R, s ∉ z.asIdeal ∧ (s : Ω) * a = r) : a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : R) : Ω) * a ∈ R
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : R) : Ω) * a ∈ R
        simp
      smul_mem' := fun c u hu => by
        show ((c • u : R) : Ω) * a ∈ R
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem c.2 hu }
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : R) : Ω) * a ∈ R := h1
    simpa using h2
  · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, s, hs, e⟩ := h ⟨P, hP.isPrime⟩
    exact absurd (hIP (show (s : Ω) * a ∈ R from e ▸ r.2)) hs

end PositivityTheory.Xgn.SequenceFamilyPairing

theorem PositivityTheory.Xgn.sequence_family_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (u : Module.Dual Ω 𝔐.Li), u ∈ P.Dh.om → ∀ v : 𝔐.Li, (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → v ∈ 𝔐.M.lat q) → u v ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd _ p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ G c' hc' P u
    hu v hv
  rw [P.isHT.1] at hu
  obtain ⟨u₀, rfl⟩ := hu
  refine PositivityTheory.Xgn.SequenceFamilyPairing.mem_of_frac _ _ fun z => ?_
  obtain ⟨h1, h2, -⟩ := PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G
    c' hc' P z
  exact PositivityTheory.Xgn.SequenceFamilyPairing.val_frac 𝔐.t.semi.smooth 𝔐.ξ (algebraMap (CR O y c') Ω)
    Subtype.val_injective P.x P.x_gen z (𝔐.all _) P.M 𝔐.M P.toLi P.toLi_pt u₀ (P.j u₀) (P.j_apply u₀) v (hv _ h1 h2)
end

