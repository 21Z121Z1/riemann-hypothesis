import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCovers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocus

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodTate

theorem exists_pairing_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    [Nontrivial D.La] : ∃ a b, D.EF a b = 1 := by
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (b.coord i)
  exact ⟨a, b i, by rw [ha]; simp⟩

def rt (n : ℕ) (x : ℤ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n)) (Complex.exp_ne_zero _)

theorem rt_val (n : ℕ) (x : ℤ) : (rt n x : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n) := rfl

theorem rt_mul (n : ℕ) (x y : ℤ) : rt n (x * y) = rt n x ^ y := by
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val, rt_val, rt_val, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem rt_congr {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ x - y) : rt n x = rt n y := by
  obtain ⟨c, hc⟩ := h
  apply Units.ext
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rt_val, rt_val, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [sub_eq_iff_eq_add.1 hc]
  push_cast
  field_simp
  ring

theorem rt_pow {n m : ℕ} (hm : 0 < m) (x : ℤ) : rt (n * m) x ^ m = rt n x := by
  apply Units.ext
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Units.val_pow_eq_pow_val, rt_val, rt_val, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [← div_div, mul_div_cancel₀ _ hm']

theorem rt_prim {n : ℕ} (hn : 0 < n) {x : ℤ} (h : IsCoprime x n) : IsPrimitiveRoot (rt n x) n := by
  rw [← IsPrimitiveRoot.coe_units_iff, rt_val]
  have := Complex.isPrimitiveRoot_exp_of_isCoprime (-x) n hn.ne' h.neg_left
  convert this using 2
  push_cast
  ring

theorem pre_injective {k : Type} [Field k] (β : ℂ →+* k) (A : Over (Sp ℂ)) :
    Function.Injective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A => toUnit (Over.mk (spMap β)) ≫ x := by
  intro x y h
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    letI := β.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap β) := ⟨fun p => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap β) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [Over.comp_left, e] at h'
  exact (cancel_epi (spMap β)).1 h'

theorem pre_onto (hM : Out.MulNSt) {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (Q : Out.PolAV (Sp ℂ))
    {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap β) ⟶ Q.A) (hx : x ^ n = 1) :
    ∃ y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, y ^ n = 1 ∧ toUnit _ ≫ y = x := by
  have hk : (n : k) ≠ 0 := by
    rw [← map_natCast β]
    exact (map_ne_zero β).2 (by exact_mod_cast hn.ne')
  have c₁ := (hM _ Q n hn).2.2.2.2 k (spMap β) hk
  have c₀ : Nat.card {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} = n ^ (2 * Q.g) :=
    (hM _ Q n hn).2.2.2.2 ℂ (𝟙 _) (by exact_mod_cast hn.ne')
  have : Finite {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₁]; positivity)
  let F : {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    fun y => ⟨toUnit _ ≫ y.1, by
      have := map_pow (preHom (G := Q.A) (toUnit (Over.mk (spMap β)))) y.1 n
      rw [y.2, map_one] at this
      exact this.symm⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective β Q.A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁])).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (β : ℂ →+* k) (c : ℂˣ) :
    Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map β.toMonoidHom c) := by
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  rw [e]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

end GlobalTheory.PeriodTate

namespace GlobalTheory

open PeriodTate in

theorem exists_tateIso_of_periods : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D'.La →+ (Fin g → ℂ)) (Q : Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) Q.A) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), 1 ≤ D.p + D.q → IsPeriod D' ty P → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ P.range) → (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs Q.A Q.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) → (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : ℂ →+* k), ∃ I : TateIso D k (Over.mk (spMap β) ⟶ Q.A) (fun a x => x ≫ act.act a) (fun n x x' c => Out.WeilIs Q.A Q.L n x x' (unitOn c)), (∀ n : ℕ, (I.ζ n : k) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n))) ∧ ∀ (n : ℕ) a, I.ev n a = toUnit _ ≫ e ((n : ℂ)⁻¹ • P (f n a)) := by
  intro hL E _ _ _ H D D' g ty P Q act e f ν hpq hP hadd hsurj hker hact hW htow hmod hν k _ _ β
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := exists_pairing_one D
  have : Nontrivial D'.La := by
    refine ⟨f 2 a₀, 0, fun h => ?_⟩
    obtain ⟨c, hc⟩ := ((hmod 2 two_pos).1 a₀).1 ⟨0, by rw [h, smul_zero]⟩
    rw [hc, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
    omega
  obtain ⟨a₁, b₁, h₁⟩ := exists_pairing_one D'
  have hcong : ∀ (n : ℕ) (a b c d : D'.La), (n : ℤ) ∣ D'.EF (a + n • c) (b + n • d) - D'.EF a b := by
    intro n a b c d
    refine ⟨D'.EF a d + D'.EF c b + n * D'.EF c d, ?_⟩
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hcop : ∀ n : ℕ, 0 < n → IsCoprime (ν n) n := by
    intro n hn
    obtain ⟨a, c, ha⟩ := (hmod n hn).2 a₁
    obtain ⟨b, d, hb⟩ := (hmod n hn).2 b₁
    obtain ⟨u, hu⟩ := hcong n (f n a) (f n b) c d
    obtain ⟨v, hv⟩ := hν n hn a b
    rw [← ha, ← hb, h₁] at hu
    exact ⟨D.EF a b, u + v, by linear_combination -hu - hv⟩
  have hνt : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
    intro n m hn hm
    obtain ⟨c, hc⟩ := htow n m hn hm a₀
    obtain ⟨d, hd⟩ := htow n m hn hm b₀
    obtain ⟨u, hu⟩ := hcong n (f n a₀) (f n b₀) c d
    obtain ⟨v, hv⟩ := hν n hn a₀ b₀
    obtain ⟨w, hw⟩ := hν (n * m) (Nat.mul_pos hn hm) a₀ b₀
    rw [← hc, ← hd] at hu
    rw [h₀] at hv hw
    push_cast at hw
    exact ⟨u + v - m * w, by linear_combination hu + hv - hw⟩
  let e' : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  let ρ := preHom (G := Q.A) (toUnit (Over.mk (spMap β)))
  have hρ : Function.Injective ρ := pre_injective β Q.A
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • P (a + n • c)) = e ((n : ℂ)⁻¹ • P a) := by
    intro n hn a c
    rw [map_add, smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map β.toMonoidHom (rt n (ν n))
            ζ_prim := fun n hn => (rt_prim hn (hcop n hn)).map_of_injective (Units.map_injective β.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, rt_pow hm, rt_congr hn (hνt n m hn hm)]
            ev := fun n a => ρ (e ((n : ℂ)⁻¹ • P (f n a)))
            add := fun n a b => by rw [map_add, map_add, smul_add, hadd, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun n => rfl, fun n a => rfl⟩
  · show toUnit (Over.mk (spMap β)) ≫ _ = (toUnit (Over.mk (spMap β)) ≫ _) ≫ _
    rw [Category.assoc, ← hact, map_smul]
    congr 2
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hP.1, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [map_eq_one_iff ρ hρ, hker, ← (hmod n hn).1 a]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc, hsm n hn])⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := pre_onto hL.mulN β Q hn x hx
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hmod n hn).2 a'
      refine ⟨a, congrArg ρ ?_⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    rw [← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul, hsm m hm, hc, hshift n hn]
  · have h := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB (toUnit (Over.mk (spMap β)))
      (hW n (f n a) (f n b) (rt n _) hn (rt_val _ _))
    rw [unitOn_pull, rt_congr hn (hν n hn a b), rt_mul, map_zpow] at h
    exact h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem existsUnique_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩

theorem hom_ext {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl

theorem exists_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem exists_mem (hU : iSup U = ⊤) (s : S) : ∃ i, s ∈ U i :=
  TopologicalSpace.Opens.mem_iSup.1 (show s ∈ iSup U by rw [hU]; trivial)

theorem isOpenImmersion {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) : IsOpenImmersion ψ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

theorem mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact (q z).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h x ⟨p x, hx⟩ rfl
    exact ⟨z, hz⟩

theorem covers (hU : iSup U = ⊤) {X : Scheme.{0}} {Z : I → Scheme.{0}} {p : X ⟶ S} {q : ∀ i, Z i ⟶ (U i).toScheme}
    {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι) (x : X) : ∃ i, x ∈ Set.range (ψ i) :=
  (exists_mem hU (p x)).imp fun i hi => (mem_range (h i) x).2 hi

theorem over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by
  ext1
  refine hom_ext (fun i => (T.hom ⁻¹ᵁ U i).ι) (fun _ => inferInstance)
    (covers hU fun i => (isPullback_morphismRestrict T.hom (U i)).flip) fun i => ?_
  exact congrArg (fun z => z.left) (h i (Over.mk (T.hom ∣_ U i))
    (Over.homMk (T.hom ⁻¹ᵁ U i).ι (morphismRestrict_ι _ _).symm))

theorem exists_lift {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩

theorem lift_ext {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.InvField

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  rw [pbT_of_le (𝟙 Y) (O := O) (O₀ := O) le_rfl]
  exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 Y) (U := O))).trans rfl

theorem pbT_eq_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O : Y.Opens} (s : Γ(Y, O)) :
    pbT f s (f ⁻¹ᵁ O) = (f.app O).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.appLE_eq_app]

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) (a b : R) : constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R)
    (O : Y.Opens) : constFn q O 0 = 0 := by
  simp [constFn]

theorem aux {K : Type} [Field K] {Y Y' : Scheme.{0}} (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ T : Y' ⟶ Y)
    (j : Y ⟶ Y') (hp : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (hρ : j ≫ ρ = 𝟙 Y)
    (hπ : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) (hT : j ≫ T = 𝟙 Y) (hq : T ≫ q = ρ ≫ q)
    (P : (∀ W : Y.Opens, Γ(Y, W) → Γ(Y, W)) → Prop)
    (hP : ∀ dd, P dd ↔ ∀ (W : Y.Opens) (f : Γ(Y, W)), pbT T f (ρ ⁻¹ᵁ W) =
      pbT ρ f (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ (dd W f) (ρ ⁻¹ᵁ W)) :
    (∃ dd, P dd) ∧ ∀ dd, P dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(Y, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn q W a) = 0) ∧ ∀ dd', P dd' → dd' = dd := by
  obtain ⟨hO, -, hex⟩ := GlobalTheory.T.const_thickening_field_structure K Y Y' q π ρ j hp hρ hπ
  have hTW : ∀ W : Y.Opens, ρ ⁻¹ᵁ W ≤ T ⁻¹ᵁ W := fun W => by
    have := hO (T ⁻¹ᵁ W)
    rw [← Scheme.Hom.comp_preimage j T, hT, Scheme.Hom.id_preimage] at this
    exact this.le
  have hjW : ∀ W : Y.Opens, W ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ W) := fun W => by
    rw [← Scheme.Hom.comp_preimage, hρ, Scheme.Hom.id_preimage]
  have uniq : ∀ (W : Y.Opens) (a b b' : Γ(Y, W)),
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b (ρ ⁻¹ᵁ W) =
      pbT ρ a (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ b' (ρ ⁻¹ᵁ W) → b = b' := by
    intro W a b b' h
    simp only [pbT_eq_app] at h
    have := (hex W _).unique (y₁ := (a, b)) (y₂ := (a, b')) rfl h
    exact congrArg Prod.snd this
  have hee : ∀ O, constFn π O DualNumber.eps * constFn π O DualNumber.eps = 0 := fun O => by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  refine ⟨?_, fun dd hd => ?_⟩
  · choose ab hab using fun W (f : Γ(Y, W)) => (hex W (pbT T f (ρ ⁻¹ᵁ W))).exists
    refine ⟨fun W f => (ab W f).2, (hP _).2 fun W f => ?_⟩
    have h := hab W f
    rw [← pbT_eq_app, ← pbT_eq_app] at h
    have h' := congrArg (fun s => pbT j s W) h
    simp only [pbT_add, pbT_mul] at h'
    rw [pbT_pbT j T (hTW W) (hjW W), pbT_pbT j ρ le_rfl (hjW W), hT, hρ, pbT_id, pbT_id,
      pbT_constFn π j (hjW W), hπ, constFn_spMap] at h'
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom DualNumber.eps = 0 := by simp
    rw [e, constFn_zero, zero_mul, add_zero] at h'
    rw [h, ← h']
  · have hd' := (hP _).1 hd
    refine ⟨fun W f f' => uniq W (f + f') _ _ ?_, fun W f f' => uniq W (f * f') _ _ ?_,
      fun W W' f h => uniq W' (rsT f W') _ _ ?_, fun W a => uniq W (constFn q W a) _ _ ?_, fun dd' hd₁ => ?_⟩
    · rw [← hd', pbT_add, hd', hd', pbT_add, pbT_add]; ring
    · rw [← hd', pbT_mul, hd', hd', pbT_add, pbT_mul, pbT_mul, pbT_mul]
      linear_combination (pbT ρ (dd W f) (ρ ⁻¹ᵁ W) * pbT ρ (dd W f') (ρ ⁻¹ᵁ W)) * hee (ρ ⁻¹ᵁ W)
    · have h1 : ρ ⁻¹ᵁ W' ≤ ρ ⁻¹ᵁ W := ρ.preimage_mono h
      rw [← hd', pbT_rsT T h (hTW W'), pbT_rsT ρ h le_rfl, pbT_rsT ρ h le_rfl, ← rsT_pbT T (hTW W) h1, hd',
        rsT_add, rsT_mul, rsT_pbT ρ le_rfl h1, rsT_pbT ρ le_rfl h1, rsT_constFn π h1]
    · rw [← hd', pbT_constFn q T (hTW W), pbT_constFn q ρ le_rfl, hq, pbT_zero, mul_zero, add_zero]
    · funext W f
      exact uniq W f _ _ (((hP _).1 hd₁ W f).symm.trans (hd' W f))

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  intro K _ A₀ _ v hv
  let s : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hs : s ≫ v = η[A₀] := Over.OverMorphism.ext hv
  let j : A₀ ⟶ epsR K ⊗ A₀ := lift (toUnit A₀ ≫ s) (𝟙 A₀)
  have hT : j ≫ ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀) = 𝟙 A₀ := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.one_mul]
  refine aux A₀.hom (fst (epsR K) A₀).left (snd (epsR K) A₀).left
    ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left j.left ?_ ?_ ?_ ?_ ?_ (IsInvDer v) (fun _ => Iff.rfl)
  · exact (IsPullback.of_hasPullback (epsR K).hom A₀.hom).flip
  · rw [← Over.comp_left, lift_snd]; rfl
  · rw [← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]; rfl
  · rw [← Over.comp_left, hT]; rfl
  · rw [Over.w, Over.w]

end GlobalTheory.KS.InvField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMulMemSpanDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

open MvPolynomial in

theorem homogeneousComponent_mul_mem_span_degree {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) {d₀ d e : ℕ}
    (h₀ : d₀ ≤ d) (he : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀})
    (a : MvPolynomial σ K) :
    homogeneousComponent e (a * F) ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  induction hF using Submodule.span_induction generalizing a with
  | mem G hG =>
    obtain ⟨hGI, hG⟩ := hG
    induction a using MvPolynomial.induction_on' with
    | monomial m c =>
      have hm : (monomial m c * G).IsHomogeneous (m.degree + d₀) :=
        (isHomogeneous_monomial c rfl).mul hG
      rw [homogeneousComponent_of_mem hm]
      split_ifs with h
      · obtain ⟨m₂, hle, hdeg⟩ := Finsupp.exists_le_degree_eq m (d - d₀) (by omega)
        obtain ⟨m₁, rfl⟩ := exists_add_of_le hle
        have : (monomial (m₂ + m₁) c : MvPolynomial σ K) * G = monomial m₁ c * (monomial m₂ 1 * G) := by
          rw [← _root_.mul_assoc, monomial_mul, _root_.mul_one, add_comm]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨I.mul_mem_left _ hGI, ?_⟩)
        have h2 := (isHomogeneous_monomial (1 : K) hdeg).mul hG
        rwa [Nat.sub_add_cancel h₀] at h2
      · exact Ideal.zero_mem _
    | add a b ha hb => rw [add_mul, map_add]; exact Ideal.add_mem _ ha hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add]; exact Ideal.add_mem _ (hx a) (hy a)
  | smul r x _ hx => rw [smul_eq_mul, ← _root_.mul_assoc]; exact hx _

theorem cutBy_of_regular_of_zeroEstimate : ∀ (K σ Hh : Type) [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d₀ d : ℕ) (p : Hh → σ → K), d₀ ≤ d → (∀ e ≥ d₀, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀}) → (∀ F ∈ I, ∀ h, MvPolynomial.eval (p h) F = 0) → (∀ F : MvPolynomial σ K, F.IsHomogeneous d → (∀ h, MvPolynomial.eval (p h) F = 0) → F ∈ I) → CutBy I Q d p := by
  intro K σ Hh _ I Q d₀ d p h₀ hreg hvan hzero e he
  have hV : vanIdeal d p = Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    unfold vanIdeal
    congr 1
    ext F
    exact ⟨fun h => ⟨hzero F h.1 h.2, h.1⟩, fun h => ⟨h.2, hvan F h.1⟩⟩
  refine ⟨(hreg e (h₀.trans he)).1, fun F hF => ⟨fun hI => ?_, fun h => ?_⟩⟩
  · have h := homogeneousComponent_mul_mem_span_degree I h₀ he ((hreg e (h₀.trans he)).2 F hI hF) 1
    rw [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hF, if_pos rfl] at h
    rwa [hV]
  · rw [hV] at h
    exact (Ideal.span_le.2 fun G hG => hG.1) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCoversStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.kunneth_symm_product_affine_covers : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))), (∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  first | exact @GlobalTheory.KS.Kunneth.kunneth_symm | exact GlobalTheory.KS.Kunneth.kunneth_symm | (intros; apply GlobalTheory.KS.Kunneth.kunneth_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_regular_on_section_nonzeroLocus : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by
  first | exact @GlobalTheory.primitive_regular_on_nonzeroLocus | exact GlobalTheory.primitive_regular_on_nonzeroLocus | (intros; apply GlobalTheory.primitive_regular_on_nonzeroLocus <;> assumption)
end

