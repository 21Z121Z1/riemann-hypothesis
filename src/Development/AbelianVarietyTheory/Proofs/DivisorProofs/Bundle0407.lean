import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

def homShEval (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) (m : M) : X ⟶ J :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom m
          map_add' := fun x y => by
            rw [(f.hom.app U).hom.map_add]; rfl
          map_smul' := fun r x => by
            rw [(f.hom.app U).hom.map_smul]; rfl }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have h := congrArg (fun k => (show M ⟶ J.obj.obj V from k).hom m)
          (congrArg (fun k => (ModuleCat.Hom.hom k) x) (f.hom.naturality g))
        exact h }⟩

def homShCurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) :
    M →ₗ[ULift.{1} R] (X ⟶ J) where
  toFun m := homShEval J X M f m
  map_add' m n := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_add m n
  map_smul' r m := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_smul r m

def homShUncurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (l : M →ₗ[ULift.{1} R] (X ⟶ J)) :
    X ⟶ (homSh J).obj (op M) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from ModuleCat.ofHom
            { toFun := fun m => ((l m).hom.app U).hom x
              map_add' := fun m n => by rw [l.map_add]; rfl
              map_smul' := fun r m => by rw [l.map_smul]; rfl })
          map_add' := fun x y => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_add x y
          map_smul' := fun r x => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_smul r x }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        exact congrArg (fun k => (ModuleCat.Hom.hom k) x) ((l m).hom.naturality g) }⟩

def homShEquiv (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) :
    (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)) where
  toFun := homShCurry J X M
  invFun := homShUncurry J X M
  left_inv f := by
    apply Sheaf.hom_ext; ext U x
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    rfl
  right_inv l := by
    apply LinearMap.ext; intro m
    apply Sheaf.hom_ext; ext U x
    rfl

theorem homShEquiv_natural_left (J X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N)
    (f : X ⟶ (homSh J).obj (op N)) :
    homShEquiv J X M (f ≫ (homSh J).map p.op) = (homShEquiv J X N f) ∘ₗ p.hom := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homShEquiv_natural_right (J X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y)
    (f : Y ⟶ (homSh J).obj (op M)) :
    homShEquiv J X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (homShEquiv J Y M f) := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homSh_curry : ∀ (R : Type) [CommRing R] (J : Shv R), ∃ e : ∀ (X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)), (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)), (∀ (X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N) (f : X ⟶ (homSh J).obj (op N)), e X M (f ≫ (homSh J).map p.op) = (e X N f) ∘ₗ p.hom) ∧ (∀ (X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y) (f : Y ⟶ (homSh J).obj (op M)), e X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (e Y M f)) :=
  fun _ _ J => ⟨homShEquiv J, homShEquiv_natural_left J, fun X Y M i f => homShEquiv_natural_right J X Y M i f⟩

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionVirtualCharacterPrime
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
namespace GlobalTheory.Shin

theorem tensorInd_virt_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hp hs χ hχ
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    exact mem_zpowers_of_prime_card rfl hs
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G χ).1 hχ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb
  obtain ⟨Z, hZ, hZ1, hZ2⟩ := GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b
    ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩)
    ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G).1, by simp⟩)
  have hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hA
  have hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hB
  refine ⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩
  · intro g
    simp only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]
    ring
  · intro δ
    simp only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧ ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  first | (exact @GlobalTheory.PD.isTop_exists_and_eq) | (exact GlobalTheory.PD.isTop_exists_and_eq) | (intros; apply GlobalTheory.PD.isTop_exists_and_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCellStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_inCell' : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))), ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  first | exact @GlobalTheory.KSp.exists_translate_inCell | exact GlobalTheory.KSp.exists_translate_inCell | (intros; apply GlobalTheory.KSp.exists_translate_inCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLatticesStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_of_stable_lattices : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  first | exact @GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | exact GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | (intros; apply GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEq
section
open Polynomial Matrix GlobalTheory.LatOrb

noncomputable section

namespace GlobalTheory.LatOrb

variable {K : Type} [Field K] {n : ℕ}

theorem exists_mul_eq_one_mem {B : Type} [Ring B] [Algebra K B] (S : Subalgebra K B)
    [FiniteDimensional K S] {a : B} (ha : a ∈ S) (hc : ∀ b : B, a * b = 0 → b = 0) :
    ∃ b ∈ S, a * b = 1 := by
  let f : S →ₗ[K] S := LinearMap.mulLeft K (⟨a, ha⟩ : S)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    exact hc x.1 (by simpa [f] using congrArg Subtype.val hx)
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact ⟨b.1, b.2, by simpa [f] using congrArg Subtype.val hb⟩

theorem conjTranspose_mem_adjoin (σ : K →+* K) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : (γ.map σ)ᵀ * γ = 1) {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ Algebra.adjoin K {γ}) :
    (a.map σ)ᵀ ∈ Algebra.adjoin K {γ} := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨b, hbm, hb⟩ := exists_mul_eq_one_mem (Algebra.adjoin K {x}) (Algebra.subset_adjoin rfl)
      (fun b hb => by rw [← Matrix.one_mul b, ← hγ, Matrix.mul_assoc, hb, Matrix.mul_zero])
    have : (x.map σ)ᵀ = b := by
      calc (x.map σ)ᵀ = (x.map σ)ᵀ * (x * b) := by rw [hb, Matrix.mul_one]
        _ = b := by rw [← Matrix.mul_assoc, hγ, Matrix.one_mul]
    rw [this]; exact hbm
  | algebraMap r =>
    have : ((algebraMap K (Matrix (Fin n) (Fin n) K) r).map σ)ᵀ =
        algebraMap K (Matrix (Fin n) (Fin n) K) (σ r) := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul, Matrix.transpose_mul]; exact mul_mem hy hx

theorem aeval_map_mulVec_mem {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (γ : Matrix (Fin n) (Fin n) K) (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [Polynomial.map_add, map_add, Matrix.add_mulVec]
    exact add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    have hk : ∀ k : ℕ, γ ^ k *ᵥ v ∈ M := by
      intro k
      induction k with
      | zero => simpa using hv
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hM _ ih
    rw [Polynomial.map_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, algebraMap_smul]
    exact M.smul_mem a (hk k)

theorem matLat_le {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (u : Matrix (Fin n) (Fin n) K) (hu : ∀ v ∈ M, u *ᵥ v ∈ M) : matLat O u M ≤ M := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_matLat u M v).mp hv
  exact hu w hw

theorem matLat_mono {O : Type} [CommRing O] [Algebra O K] {M N : Submodule O (Fin n → K)}
    (u : Matrix (Fin n) (Fin n) K) (h : M ≤ N) : matLat O u M ≤ matLat O u N :=
  Submodule.map_mono h

end GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem exists_unitary_matLat_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧
      matLat O t M = matLat O (aeval γ p) M := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar σ hσ hσO hγ M hML hMγ p hpu hpM
  set A := Algebra.adjoin K {γ} with hAdef
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    have hc : ∀ a ∈ ({γ} : Set (Matrix (Fin n) (Fin n) K)), ∀ b ∈ ({γ} : Set _), a * b = b * a := by
      intro a ha b hb; rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
    letI : CommRing A := Algebra.adjoinCommRingOfComm K hc
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : A) ⟨v, hv⟩)
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb; rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb])
  have hstar : ∀ a ∈ A, (a.map σ)ᵀ ∈ A := fun a ha => conjTranspose_mem_adjoin σ γ hγ ha
  let τ : A →+* A :=
    { toFun := fun a => ⟨(a.1.map σ)ᵀ, hstar a.1 a.2⟩
      map_one' := by
        apply Subtype.ext
        show (((1 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 1
        rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a.1 * b.1).map σ)ᵀ = (a.1.map σ)ᵀ * (b.1.map σ)ᵀ
        rw [Matrix.map_mul, Matrix.transpose_mul]
        exact hcomm _ (hstar b.1 b.2) _ (hstar a.1 a.2)
      map_zero' := by
        apply Subtype.ext
        show (((0 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 0
        rw [Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero]
      map_add' := fun a b => by
        apply Subtype.ext
        show ((a.1 + b.1).map σ)ᵀ = (a.1.map σ)ᵀ + (b.1.map σ)ᵀ
        rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add] }
  have hτv : ∀ a : A, (τ a).1 = (a.1.map σ)ᵀ := fun a => rfl
  have hττ : ∀ a, τ (τ a) = a := by
    intro a; apply Subtype.ext
    rw [hτv, hτv, Matrix.transpose_map, Matrix.map_map, Matrix.transpose_transpose]
    ext i j; simp [hσ]
  have hτk : ∀ k, τ (algebraMap K A k) = algebraMap K A (σ k) := by
    intro k; apply Subtype.ext
    rw [hτv]
    show ((algebraMap K (Matrix (Fin n) (Fin n) K) k).map σ)ᵀ = algebraMap K (Matrix (Fin n) (Fin n) K) (σ k)
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

  have hred : IsReduced A := by
    constructor
    rintro a ⟨k, hk⟩
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have h1 : aeval γ (q ^ k) = 0 := by
      rw [map_pow, hq]; exact congrArg Subtype.val hk
    have hsep : (minpoly K γ).Separable :=
      ((show P₀.Separable from hcop).map (f := algebraMap O K)).of_dvd
        (hchar ▸ Matrix.minpoly_dvd_charpoly γ)
    have h2 : minpoly K γ ∣ q := hsep.squarefree.isRadical k q (minpoly.dvd K γ h1)
    apply Subtype.ext
    rw [← hq]
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K γ)

  have hxA : aeval γ p ∈ A := Polynomial.aeval_mem_adjoin_singleton K γ
  obtain ⟨b, hbA, hb⟩ := exists_mul_eq_one_mem A hxA (fun b hb => by
    obtain ⟨u, hu⟩ := hpu
    rw [← hu] at hb
    rw [← Matrix.one_mul b, ← u.inv_mul, Matrix.mul_assoc, hb, Matrix.mul_zero])
  let x : Aˣ := Units.mkOfMulEqOne (⟨aeval γ p, hxA⟩ : A) ⟨b, hbA⟩ (Subtype.ext hb)
  have hxv : ((x : A) : Matrix (Fin n) (Fin n) K) = aeval γ p := rfl
  let ι : A →ₐ[O] Matrix (Fin n) (Fin n) K := (A.val).restrictScalars O
  have hι : ∀ a : A, IsIntegral O a ↔ IsIntegral O a.1 := fun a =>
    (isIntegral_algHom_iff ι Subtype.val_injective).symm

  have hcM : ∀ v ∈ M, (τ x * x : A).1 *ᵥ v ∈ M := by
    intro v hv
    have : (τ x * x : A).1 *ᵥ v ∈ matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M :=
      (mem_matLat _ _ _).mpr ⟨v, hv, rfl⟩
    rwa [hpM] at this
  have hcinv : (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) * (τ x * x) = 1 := by
    rw [mul_mul_mul_comm, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hc'M : ∀ v ∈ M, (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ v ∈ M := by
    intro v hv
    rw [← hpM] at hv
    obtain ⟨u, hu, rfl⟩ := (mem_matLat _ _ _).mp hv
    have e : ((τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ ((((aeval γ p).map σ)ᵀ * aeval γ p) *ᵥ u)) = u := by
      rw [Matrix.mulVec_mulVec]
      have := congrArg Subtype.val hcinv
      exact (congrArg (· *ᵥ u) this).trans (Matrix.one_mulVec u)
    rw [e]; exact hu
  have hi1 : IsIntegral O (τ (x : A) * x) := (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hcM)
  have hi2 : IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) :=
    (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hc'M)
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit σ hσO τ hττ hτk x hi1 hi2

  have hkeep : ∀ a : A, IsIntegral O a → ∀ v ∈ M, a.1 *ᵥ v ∈ M := by
    intro a ha
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have ha' : IsIntegral O (aeval γ q) := hq ▸ (hι a).mp ha
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar q ha'
    rw [← hq, hr]
    exact aeval_map_mulVec_mem M γ hMγ r
  have hk1 := hkeep _ ht2
  have hk2 := hkeep _ ht3
  refine ⟨(t : A).1, congrArg Subtype.val ht1, hcomm _ (t : A).2 _ (Algebra.subset_adjoin rfl), ?_⟩
  apply le_antisymm
  · have e : (t : A).1 = (aeval γ p) * ((t : A) * ((x⁻¹ : Aˣ) : A)).1 := by
      rw [← hxv]
      show (t : A).1 = ((x : A) * ((t : A) * ((x⁻¹ : Aˣ) : A))).1
      rw [mul_comm (t : A), ← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk1)
  · have e : aeval γ p = (t : A).1 * (((t⁻¹ : Aˣ) : A) * (x : A)).1 := by
      rw [← hxv]
      show ((x : A)).1 = ((t : A) * (((t⁻¹ : Aˣ) : A) * (x : A))).1
      rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk2)

end GlobalTheory.LatOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFilteredStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorWedgeEqOfLocalizedSpanStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_wedge_eq_of_localized_span : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  first | (exact @GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (exact GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (intros; apply GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNormsStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.EtaleCls.classes_mod_rat_norms) | (exact GlobalTheory.EtaleCls.classes_mod_rat_norms) | (intros; apply GlobalTheory.EtaleCls.classes_mod_rat_norms  <;> assumption)
end

