import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricBundleTrivialConstantFamilyDualNumber
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionGenus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_eq_iff (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ y, a = b + n • y := by
  rw [tateIso_ev_eq_iff I hn]
  unfold Datum.ModN
  exact exists_congr fun y => sub_eq_iff_eq_add'

theorem exists_lift (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  have hs : ∀ a, ∃ b, I'.ev n b = I.ev n a := fun a => (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
  choose s hs using hs
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • (LinearMap.id : D'.La →ₗ[𝓞 E] D'.La))
  have hN : ∀ a b : D'.La, N.mkQ a = N.mkQ b ↔ I'.ev n a = I'.ev n b := by
    intro a b
    rw [tateIso_ev_eq_iff I' hn, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  let φ : D.La →ₗ[𝓞 E] D'.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add, hN, I'.add, hs, hs, hs, I.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, hN, I'.lin, hs, hs, I.lin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ φ N.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [(hN _ _).1 h, hs]

theorem genus_of_tateIso
    (he : ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c')
    (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      ((∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
      ∀ n, 0 < n → I.ζ n = I'.ζ n ^ ν n ∧ ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := exists_lift I' I h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · have : NeZero n := ⟨h.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n h).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n h).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, ν, ⟨?_, ?_, ?_⟩, fun n hn => ⟨hν n hn, hf n hn⟩⟩
  · intro n m hn hm a
    rw [← ev_eq_iff I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun x => ?_, fun x' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨x, hx⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn x')
      refine ⟨x, (ev_eq_iff I' hn _ _).1 ?_⟩
      rw [← hf n hn, hx]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ hn (tateIso_ev_pow I' hn _) (tateIso_ev_pow I' hn _) e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have h1 := congrArg (fun x : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x.val) h
  apply Units.ext
  simpa [unitOn] using h1

noncomputable def expRoot (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem expRoot_zpow (n : ℕ) (m : ℤ) :
    ((expRoot n ^ m : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expRoot, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem expRoot_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expRoot n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rw [← Complex.exp_neg] at h
  rw [expRoot, Units.val_mk0, neg_div]
  exact h

theorem expRoot_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expRoot (n * m) ^ m = expRoot n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, expRoot, expRoot, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

section

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

end

noncomputable def periodTateIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H)
    {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (act : OAct (𝓞 E) A)
    (Q : D'.La →+ (Fin g → ℂ)) (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range)
    (hact : ∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a)
    (hW : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs A L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c)) :
    TateIso D' ℂ (𝟙_ (Over (Sp ℂ)) ⟶ A) (fun c y => y ≫ act.act c)
      (fun n y y' c => Out.WeilIs A L n y y' (unitOn c)) where
  ζ := expRoot
  ζ_prim _ hn := expRoot_prim hn
  ζ_pow _ _ hn hm := expRoot_pow hn hm
  ev n x := u.ex ((n : ℂ)⁻¹ • Q x)
  add n a b := by rw [map_add, smul_add, u.ex_add]
  lin n c a := hact c n a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [u.ker, hΛ]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hQ ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [← ex_nsmul, u.ker, hΛ] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, smul_smul, inv_mul_cancel₀ hn', one_smul]⟩
    · rintro ⟨a, rfl⟩
      rw [← ex_nsmul, u.ker, hΛ, smul_smul, mul_inv_cancel₀ hn', one_smul]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← ex_nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hW n a b _ hn (expRoot_zpow n _)

theorem period_lattice_in_genus :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' P u Hm χ act Q hp hq hAH hQ hΛ hE hact I
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hT hU P u Hm χ hAH
  have hW' : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c) := by
    intro n a b c hn hc
    refine hW n ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
    have h := hEf ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [hE] at h
    rw [Int.cast_injective h]
    exact hc
  obtain ⟨f, ν, ⟨h1, h2, h3⟩, h4⟩ := genus_of_tateIso (D := D) (D' := D')
    (fun n x y c c' _ hx hy ha hb =>
      unitOn_injective (((hL.weil _ P n (Over.mk (𝟙 (Sp ℂ)))).1 x y hx hy).unique ha hb))
    (periodTateIso D' u act Q hQ hΛ hact hW') I
  refine ⟨f, ν, ⟨hp, hq, h1, h2, h3⟩, fun n hn => ⟨?_, fun x => ?_⟩⟩
  · rw [(h4 n hn).1]
    exact expRoot_zpow n _
  · rw [(h4 n hn).2]
    rfl

end GlobalTheory.TorsionGenus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowLeftCompOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanning
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FibreEmbed

open GlobalTheory.AmpleSpan GlobalTheory.SegreCoord GlobalTheory.ProjSpace GlobalTheory.Cartier TopologicalSpace

theorem embedsBy_fibre (hA : Out.AmpleSt) (hB : Out.PolBaseChangeSt) {S : Scheme.{0}} (P : Out.PolAV S) {K : Type}
    [Field K] (x : Sp K ⟶ S) {N : ℕ} (hN : 4 ≤ N) {I : Type} [Fintype I]
    (t : I → LB.Sec (Out.LPow P.A P.L N (Over.mk x)))
    (ht : Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Over.mk x))) = ⊤) :
    EmbedsBy (fst (Over.mk x) P.A).left t := by
  obtain ⟨P', g, hg, -, -, w⟩ := hB S _ x P
  have h : IsPullback (snd (Over.mk x) P.A).left (fst (Over.mk x) P.A).left P.A.hom x :=
    (IsPullback.of_hasPullback x P.A.hom).flip
  let e := h.isoIsPullback _ _ hg
  have he : e.hom ≫ g = (snd (Over.mk x) P.A).left := h.isoIsPullback_hom_fst _ _ hg
  have he' : e.hom ≫ P'.A.hom = (fst (Over.mk x) P.A).left := h.isoIsPullback_hom_snd _ _ hg
  have haff : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Sp K))
  have sq : IsPullback e.hom (fst (Over.mk x) P.A).left P'.A.hom
      ((𝟙 (Sp K) ≫ (Sp K).topIso.inv) ≫ Scheme.Opens.ι (⊤ : (Sp K).Opens)) := by
    rw [comp_topIso_inv_ι]
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id (Sp K))
      ⟨he'.trans (Category.comp_id _).symm⟩
  obtain ⟨M, s, hs⟩ := exists_embedsBy_of_isPullback P'.A P'.isLB (hA _ P' N hN).2 (isAffineOpen_top _) sq
    (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  obtain ⟨w', hw'⟩ := LBIso.symm w
  have hP := DVR.linComb_isLB P'.L P'.isLB (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))
  have hQ : (Out.LPow P.A P.L N (Over.mk x)).IsLB := DVR.linComb_isLB P.L P.isLB _ _
  obtain ⟨W, hW⟩ : LBIso (Out.LPow P.A P.L N (Over.mk x))
      ((LB.LinComb P'.L (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullSame P.L _ _ _ (𝟙 _) fun _ => he.symm.trans (Category.id_comp _).symm)
      (Geo.Tor.chartPullPull _ _ _ rfl)
      (LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => e.hom) (fun _ => (N : ℤ))))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hQ (s i)
  have hs₂ : EmbedsBy (fst (Over.mk x) P.A).left s' := by
    refine hs.pull (ψ := 𝟙 _) (g := 𝟙 _) IsPullback.of_id_fst fun y => ?_
    obtain ⟨j, hj⟩ := exists_chart hP y
    obtain ⟨k, hk⟩ := exists_chart hQ y
    refine ⟨j, k, hj, hk, gw W (𝟙 _) y j k, fun i => ?_⟩
    have := hs' i _ (𝟙 _) y j k hj hk
    rwa [Category.id_comp] at this
  have := P.isAb.proper
  have : UniversallyClosed (fst (Over.mk x) P.A).left :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h inferInstance
  exact hs₂.of_inSpan fun j => (inSpan_iff_mem_span P.A t _).2 (by rw [ht]; trivial)

variable {X : Scheme.{0}} {A B : LB X} {σ : Type} {a : σ → A.Sec} {b : σ → B.Sec} {T : Type} [CommRing T]
  {x : Sp T ⟶ X} {v : σ → T}

theorem gs_of_secMaps {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) (y : Sp T) {p : B.ι} {q : A.ι}
    (hp : x y ∈ B.U p) (hq : x y ∈ A.U q) :
    ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((b i).f p) = u * gs x y _ ((a i).f q) := by
  have hm : x y ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  refine ⟨gm x y (B.U p ⊓ A.U q) (w.s (p, q)), fun i => ?_⟩
  exact (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (hw i (p, q))).trans ((gs_mul x y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit x y _ hm _) (gs_res x y _ hm _))))

theorem loc_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) :
    Loc A a x v ↔ Loc B b x v := by
  refine ⟨fun h y p hp => ?_, fun h y q hq => ?_⟩
  · obtain ⟨q, hq⟩ := exists_chart hA (x y)
    obtain ⟨u, hu⟩ := h y q hq
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u' * u, fun i => by rw [hu', hu, Units.val_mul, mul_left_comm]⟩
  · obtain ⟨p, hp⟩ := exists_chart hB (x y)
    obtain ⟨u, hu⟩ := h y p hp
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u'⁻¹ * u, fun i => by rw [Units.val_mul, mul_left_comm, ← hu, hu', Units.inv_mul_cancel_left]⟩

theorem span_eq_top_of_loc (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (h : Loc A a x v) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let y : Sp T := ⟨m, hm.isPrime⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hi
  obtain ⟨u, hu⟩ := h y k hk
  have h1 := (mem_nonzeroLocus_iff_gs (a i) x y hk).1 hi
  rw [hu] at h1
  have h2 := ((Sp T).mem_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) y trivial).2
    (isUnit_of_mul_isUnit_left h1)
  have h3 := (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).le h2
  exact h3 (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem secCoord_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i))
    (ha : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (hb : ⨆ i, Out.nonzeroLocus (b i) = ⊤) :
    SecCoord A a x v ↔ SecCoord B b x v :=
  ⟨fun h => secCoord_of_loc (span_eq_top_of_loc ha (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).1 (loc_of_secCoord h)),
    fun h => secCoord_of_loc (span_eq_top_of_loc hb (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).2 (loc_of_secCoord h))⟩

theorem projRep_bot (R : Type) [CommRing R] {N : ℕ} (e : σ ≃ Fin (N + 1)) :
    ProjRep (⊥ : Ideal (MvPolynomial σ R)) (PSpace.str R N) ((O1 R N).pull (𝟙 _))
      (fun c => secPull (coord R N (e c)) (𝟙 _)) := by
  refine ⟨pull_isLB (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩
  · obtain ⟨hv, -⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx) v).1 h
    rw [ProjCoord.range_comp_symm] at hv
    exact ⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩
  · rw [← ProjCoord.range_comp_symm e] at hv
    refine ⟨pt β _ hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩
    · exact (ProjCoord.secCoord_iff e (𝟙 _) β _ (by simpa using pt_str β _ hv) v).2 ⟨hv, Category.comp_id _⟩
    · obtain ⟨_, h⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx.1) v).1 hx.2
      exact (Category.comp_id _).symm.trans h

theorem projRep_of_embedsBy {R : Type} [CommRing R] (f : X ⟶ Sp R) (hA : A.IsLB) {N : ℕ} (e : σ ≃ Fin (N + 1))
    (h : EmbedsBy f (fun j => a (e.symm j))) : ProjRep (idealOf f A a (𝟙 X)) f A a := by
  have : Finite σ := Finite.of_equiv _ e.symm
  obtain ⟨hs, hcl⟩ := (veryAmpleBy_iff f (fun j => a (e.symm j))).1 ((embedsBy_spec_iff f _).1 h)
  have key := GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ _ X (PSpace.str R N) _ _ (toProj f _ hs) A a (projRep_bot R e) hcl hA
    fun R' _ y v => by
      let c : R →+* R' := (Spec.preimage (y ≫ f)).hom
      have hc : (y ≫ toProj f _ hs) ≫ PSpace.str R N = spMap c := by
        rw [Category.assoc, toProj_str]
        exact (Spec.map_preimage (y ≫ f)).symm
      have h1 := ProjCoord.secCoord_iff e (toProj f _ hs) c y hc v
      have h2 := ProjCoord.secCoord_iff e (𝟙 _) c (y ≫ toProj f _ hs) (by rw [Category.comp_id]; exact hc) v
      rw [Category.comp_id] at h2
      refine Iff.trans ?_ (h1.trans h2.symm)
      refine (secCoord_iff_of_secMaps (pull_isLB (O1_isLB R N) _) hA (w := toProjIso f _ hs) (fun i => ?_) ?_ ?_).symm
      · simpa only [Equiv.symm_apply_apply] using secMaps_toProjIso f _ hs (e i)
      · exact (e.iSup_comp (g := fun j => Out.nonzeroLocus (secPull (coord R N j) (toProj f _ hs)))).trans
          (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) _)
      · exact (e.symm.iSup_comp (g := fun c => Out.nonzeroLocus (a c))).symm.trans hs
  rwa [toProj_str] at key

theorem projRep_fibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  intro hL _ S P K _ _ x k I _ σ hk hσ
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have hN : 4 ≤ N := by exact_mod_cast hk
  have := Fintype.ofFinite I
  have h₀ := embedsBy_fibre hL.ample hL.polBaseChange P x hN σ hσ
  have hne : Nonempty I := by
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨i, -⟩ := Opens.mem_iSup.1 (h₀.1.ge (Set.mem_univ
      ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ P.A)).left p)))
    exact ⟨i⟩
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card I = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  let e := Fintype.equivFinOfCardEq hM
  refine projRep_of_embedsBy _ (DVR.linComb_isLB P.L P.isLB _ _) e
    (embedsBy_fibre hL.ample hL.polBaseChange P x hN _ ?_)
  rw [← hσ]
  exact congrArg _ (e.symm.surjective.range_comp
    fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L N (Over.mk x)))

end GlobalTheory.FibreEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemistableReductionSplitOfPadicStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableReductionSplit_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  first | exact @GlobalTheory.SS.semistablePol_of_padic | exact GlobalTheory.SS.semistablePol_of_padic | (intros; apply GlobalTheory.SS.semistablePol_of_padic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.siegelPullback_id_comp_cancel : ∀ (h k : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s') (c'' : SiegPre h k ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), SiegPB c c (𝟙 _) ∧ (SiegPB c' c f → (SiegPB c'' c' f' ↔ SiegPB c'' c (f' ≫ f))) := by
  first | exact @GlobalTheory.SiegelPullComp.id_comp_cancel | exact GlobalTheory.SiegelPullComp.id_comp_cancel | (intros; apply GlobalTheory.SiegelPullComp.id_comp_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricBundleTrivialConstantFamilyDualNumberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (Q : LB A'.left) (k : ∀ i i', Γ(P₀.A.left, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn A'.hom _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → Out.Sym A' Q → ∃ t : Q.Gen, t.IsGen := by
  first | exact @GlobalTheory.KS.EpsSym.trivial_of_symmetric | exact GlobalTheory.KS.EpsSym.trivial_of_symmetric | (intros; apply GlobalTheory.KS.EpsSym.trivial_of_symmetric <;> assumption)
end

