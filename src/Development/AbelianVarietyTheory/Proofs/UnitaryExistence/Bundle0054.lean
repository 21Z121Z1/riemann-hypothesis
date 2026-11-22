import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisedQuotientOfCommensurable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.CommensurableQuotient

theorem card_range_eq {R M Q : Type} [Ring R] [AddCommGroup M] [Module R M] [Group Q]
    (φ : Multiplicative M →* Q) (p : Submodule R M) (h : ∀ a, φ (Multiplicative.ofAdd a) = 1 ↔ a ∈ p) :
    Nat.card φ.range = Nat.card (M ⧸ p) := by
  have e : φ.ker = AddSubgroup.toSubgroup p.toAddSubgroup := Subgroup.ext fun a => h a.toAdd
  rw [← Subgroup.index_ker, e, AddSubgroup.index_toSubgroup]
  rfl

theorem exists_point_lift {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} (ψ : A ⟶ B) [IsFinite ψ.left]
    [Surjective ψ.left] (c : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ d : 𝟙_ (Over (Sp k)) ⟶ A, d ≫ ψ = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := k) (pullback.snd ψ.left c.left)
  have hb : (u ≫ pullback.fst ψ.left c.left) ≫ ψ.left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst ψ.left c.left) ≫ A.hom = (𝟙_ (Over (Sp k))).hom := by
    rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w c
  exact ⟨Over.homMk _ hw, Over.OverMorphism.ext hb⟩

theorem smoothDim_of_etale {k : Type} [Field k] {A B : Over (Sp k)} (ψ : A ⟶ B) [Etale ψ.left] [Smooth B.hom]
    [GeometricallyConnected B.hom] (x : A.left) {g : ℕ} (hA : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension g B.hom := by
  have : ConnectedSpace (Sp k) := inferInstanceAs (ConnectedSpace (PrimeSpectrum k))
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (ψ.left x)
  have h : SmoothOfRelativeDimension (0 + d) (ψ.left ≫ B.hom) := inferInstance
  rw [Over.w ψ, zero_add] at h
  rwa [H1.dim_unique _ hA h x]

theorem isHolTo_smul_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ y) (c : ℂ) (φ : X ⟶ Y) :
    IsHolTo Set.univ (fun z => y (c • z) ≫ φ) := by
  intro U f
  obtain ⟨h₁, h₂⟩ := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  have hc : Differentiable ℂ (fun z : V => c • z) := differentiable_id.const_smul c
  refine ⟨h₁.preimage hc.continuous, ?_⟩
  simp only [← valAt'_comp]
  exact h₂.comp hc.differentiableOn fun z hz => hz

theorem exists_weilIs (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type}
    [Field k] (t : SAB H (Sp k)) [IsProper t.G.hom] {g : ℕ} (hd : SmoothOfRelativeDimension g t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) (n : ℕ) {T : Over (Sp k)} (x y : T ⟶ t.G)
    (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ c, Out.WeilIs t.G t.PP.L n x y c := by
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp k) :=
    { A := t.G, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ((hL.weil _ P n T).1 x y hx hy).exists

end GlobalTheory.CommensurableQuotient

namespace GlobalTheory

open CommensurableQuotient

theorem exists_uniformised_quotient_of_commensurable : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)), D'.p = D.p → D'.q = D.q → (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) → IsPeriod D ty P → IsPeriod D' ty P' → (∀ a, P' (j a) = (N : ℂ) • P a) → (∀ a, P (j' a) = (N : ℂ) • P' a) → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → ∃ (t' : SAB H (Sp ℂ)) (e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t'.G)), (IsProper t'.G.hom ∧ SmoothOfRelativeDimension g t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ DetCond D' t'.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ (∀ z, e' z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a) ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c)) := by
  intro hL hQ E _ _ _ H D D' g ty P P' N j j' t e hp hq ⟨hN, _, _, _, hE, hcard⟩ _ hP' hj hj'
    ⟨hpr, hsm, ham, hkt, hdet, hadd, hsurj, hker, hlin, hhol, hweil⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  let eh : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun z => e z.toAdd, map_one' := e0, map_mul' := fun z w => hadd _ _ }
  have epow : ∀ (n : ℕ) z, e z ^ n = e ((n : ℂ) • z) := fun n z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_pow eh (Multiplicative.ofAdd z) n).symm
  have esub : ∀ z w, e z = e w ↔ z - w ∈ P.range := fun z w => by
    rw [← hker, ← mul_inv_eq_one, ← div_eq_mul_inv]
    exact Eq.congr_left (map_div eh (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)).symm
  let φ : Multiplicative D'.La →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun a => e ((N : ℂ)⁻¹ • P' a.toAdd)
      map_one' := by rw [toAdd_one, map_zero, smul_zero, e0]
      map_mul' := fun a b => by rw [toAdd_mul, map_add, smul_add, hadd] }
  have hmem : ∀ x, x ∈ φ.range ↔ ∃ a, e ((N : ℂ)⁻¹ • P' a) = x := fun x => Iff.rfl
  have hrw : ∀ (k : ℕ) a, ((k * N ^ 2 : ℕ) : ℂ)⁻¹ • P (j' a) = (N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a := fun k a => by
    rw [hj', smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  have hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L ((k * N ^ 2 : ℕ) : ℤ) (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a))
        (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' b)) (unitOn c) := fun k a b c hk hc => by
    rw [← hrw, ← hrw]
    refine hweil (k * N ^ 2) (j' a) (j' b) c (by positivity) (hc.trans ?_)
    rw [hE]
    congr 1
    push_cast
    field_simp
  obtain ⟨t', ψ, hpr', ham', hkt', hψ, hfin, het, hsj, hkψ, hact, hiso⟩ :=
    hQ E H ℂ t g N φ.range hN hpr hsm ham hkt
      (by
        intro x hx c
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        refine (hmem _).2 ⟨c • a, ?_⟩
        rw [← hlin]
        congr 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, hP'.1]
        ring)
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        rw [epow, hker]
        refine ⟨j' a, ?_⟩
        rw [hj', smul_smul]
        congr 1
        push_cast
        field_simp)
      (by
        intro x hx y hy
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        obtain ⟨b, rfl⟩ := (hmem y).1 hy
        have h := hw 1 a b 1 one_pos (by
          rw [Units.val_one, Nat.cast_one, div_one, ← Complex.exp_int_mul_two_pi_mul_I (-(D'.EF a b))]
          congr 1
          push_cast
          ring)
        rw [_root_.one_mul, Nat.cast_one, inv_one, one_smul, one_smul, show unitOn (1 : ℂˣ) = 1 from map_one _] at h
        exact h)
      (by
        rw [← hcard]
        refine card_range_eq φ _ fun a => (hker _).trans ⟨?_, ?_⟩
        · rintro ⟨b, hb⟩
          refine ⟨b, hP'.2.1 ?_⟩
          rw [hj, hb, smul_inv_smul₀ hN']
          rfl
        · rintro ⟨b, rfl⟩
          exact ⟨b, by rw [toAdd_ofAdd, hj, inv_smul_smul₀ hN']⟩)
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hB := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have := hB.smooth
  have := hB.geomConnected
  have hsm' : SmoothOfRelativeDimension g t'.G.hom :=
    smoothDim_of_etale ψ ((e 0).left (default : PrimeSpectrum ℂ)) hsm
  have hker' : ∀ z, e ((N : ℂ)⁻¹ • z) ≫ ψ = 1 ↔ z ∈ P'.range := fun z => by
    rw [hkψ, hmem]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := (esub _ _).1 ha
      refine ⟨a - j b, ?_⟩
      rw [map_sub, hj, hb, ← smul_sub, smul_inv_smul₀ hN', sub_sub_cancel]
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  refine ⟨t', fun z => e ((N : ℂ)⁻¹ • z) ≫ ψ, hpr', hsm', ham', hkt', fun τ => ?_, fun z w => ?_, fun y => ?_, hker',
    fun a z => ?_, isHolTo_smul_comp hhol _ ψ.left, fun k a b c hk hc => ?_⟩
  · rw [hp, hq, ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact,
      ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact]
    exact hdet τ
  · simp only [smul_add, hadd, MonObj.mul_comp]
  · obtain ⟨x, rfl⟩ := exists_point_lift ψ y
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨(N : ℂ) • z, by simp only [inv_smul_smul₀ hN']⟩
  · beta_reduce
    rw [Category.assoc, ← hact, ← Category.assoc, ← hlin]
    congr 2
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have htor : ∀ a, (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a) ≫ ψ) ^ k = 1 := fun a => by
      rw [← MonObj.pow_comp, epow, smul_comm (k : ℂ), smul_inv_smul₀ hk', hker']
      exact ⟨a, rfl⟩
    obtain ⟨c', hc'⟩ := exists_weilIs hL t' hsm' ham' hkt' k _ _ (htor a) (htor b)
    have h₁ := (weilIs_along_hom hL.globalFns _ _ _ ψ _ _ _ _ _ _ _ c' c' hA hB t.PP.isLB t'.PP.isLB hψ hiso hc').1
    have h₂ := hw k a b c hk hc
    rw [Nat.cast_mul] at h₂
    exact CommutatorPairing.weilIs_unique hL.globalFns hA t.PP.isLB h₁ h₂ ▸ hc'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

namespace FibreMatch

theorem surjective_of_countable {V W L : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Countable L] (f : V →ₗ[ℂ] W) (P : L → W) (h : ∀ w, ∃ z a, w = f z + P a) : Function.Surjective f := by
  have hc : Countable (W ⧸ LinearMap.range f) :=
    Function.Surjective.countable (f := fun a => (LinearMap.range f).mkQ (P a)) fun q => by
      obtain ⟨w, rfl⟩ := (LinearMap.range f).mkQ_surjective q
      obtain ⟨z, a, rfl⟩ := h w
      refine ⟨a, ?_⟩
      have : (LinearMap.range f).mkQ (f z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
      simp only [map_add, this, zero_add]
  intro w
  by_contra hw
  have hq : (LinearMap.range f).mkQ w ≠ 0 := fun h0 => hw ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have : Countable ℂ := (smul_left_injective ℂ hq).countable
  exact not_countable (α := ℝ) (Complex.ofReal_injective.countable)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem countable_La (D : Datum H) : Countable D.La := by
  have := D.fin
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Finsupp.Countable.of_moduleFinite (R := 𝓞 E)

theorem fibrewise {X : Scheme.{0}} (t : SAB H (Sp ℂ)) (t' : SAB H X) (D₁ D₂ : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (n : SABMap t t' y) (hy : (𝟙_ (Over (Sp ℂ))).hom ≫ y = y')
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t'.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t'.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t'.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e z).left ≫ n.φ = (e' (h z)).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') := by
  subst hy
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  let ρ := pushHom n.cart (𝟙_ (Over (Sp ℂ)))
  have hρ : ∀ x, (ρ x).left = x.left ≫ n.cm.F := fun _ => rfl
  have ρi : Function.Injective ρ := fun x x' hx => Over.OverMorphism.ext <| n.cart.1.hom_ext
    (by rw [← hρ, ← hρ, hx]) (by rw [Over.w, Over.w])
  have ρs : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (n.cart.1.lift x.left (𝟙_ (Over (Sp ℂ))).hom (Over.w x)) (n.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (n.cart.1.lift_fst _ _ _)⟩
  let ψ : pullback t.G.hom (𝟙 (Sp ℂ)) ⟶ pullback t'.G.hom ((𝟙_ (Over (Sp ℂ))).hom ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ n.cm.F) (pullback.snd _ _) (by
      rw [Category.assoc, n.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc]
      rfl)
  have ψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ n.cm.F := pullback.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre (Sp ℂ) X t.G t'.G (𝟙 _) _ g g e e' ψ ρ t'.semi.smooth ha ha'
    hh hh' hd' dk' ψ₂ (fun x => pullback.hom_ext
      (by rw [Category.assoc, ψ₁, ← Category.assoc, UniformLift.fibPt_fst, UniformLift.fibPt_fst]; rfl)
      (by rw [Category.assoc, ψ₂, UniformLift.fibPt_snd, UniformLift.fibPt_snd]))
  have hf : ∀ z, e' (f z) = ρ (e z) := hf
  have := countable_La D₂
  have fs : Function.Surjective f := surjective_of_countable f P' fun w => by
    obtain ⟨x, hx⟩ := ρs (e' w)
    obtain ⟨z, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := (hk' _).1 ((ExpUniqFamily.eq_iff_sub e' ha' w (f z)).1 (hx.symm.trans (hf z).symm))
    exact ⟨z, a, by rw [ha]; abel⟩
  let fe := LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.2 fs, fs⟩
  obtain ⟨h, gam, h1, h2, -⟩ := ExpUniqFamily.algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1
    hP.2.1 hP'.2.1 hP.2.2.1 hP'.2.2.1 (fun z => ρ (e z)) e' (fun z w => by rw [ha, map_mul]) ha'
    (fun z => by rw [← hk, map_eq_one_iff ρ ρi]) hk' (fun a x => x ≫ t'.act.act a)
    (fun a z => by
      rw [hl]
      apply Over.OverMorphism.ext
      rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, n.act, Category.assoc])
    hl' f fe.symm hf (fun z => by
      rw [← hf]
      exact congrArg e' (fe.apply_symm_apply z))
  refine ⟨h, gam, fun z => by rw [h1, hρ], h2, fun a a' => ?_⟩
  refine ExpUniqFamily.int_eq_of_exp _ _ fun k hk0 => ?_
  have hL : LBIso t.PP.L (t'.PP.L.pull n.cm.F) := by
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨w, hw⟩
  have w1 := (weilIs_grpPullback_of_comm X (Sp ℂ) t'.G t.G y n.cm.F t'.PP.L t.PP.L t'.PP.isLB t.PP.isLB n.cart hL
    _ k _ _ (ρ _) (ρ _) _ (hρ _) (hρ _)).1 (hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl)
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t'.G t'.PP.L t'.PP.isLB ℂ _ k _ _ _ _ w2 w1)

end FibreMatch

theorem familyUnif_fibre_lattice_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (D' : Datum H) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (n : SABMap t Xo.univ.t (U.u i P)), IsPeriod (U.Di i) ty P → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ z, (e z).left ≫ n.φ = (U.ex i P (h z)).left) ∧ (∀ a, P (gam a) = h (P' a)) ∧ ∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a' := by
  intro E _ _ _ H D l Xo σ g ty U i P D' P' t e n hP hP' ⟨_, _, _, _, _, ha, hs, hk, hl, hh, hw⟩
  exact FibreMatch.fibrewise t Xo.univ.t D' (U.Di i) ty P' P hP' hP _ _ n (Category.id_comp _) e (U.ex i P) ha
    (U.ex_add i P hP) hs hk (U.ex_ker i P hP) hl (U.ex_lin i P hP) hw (U.ex_weil i P hP) hh
    (ExpUniqFamily.isHolTo_ex U i P hP) (U.ex_diff i P hP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.RiemannForm

theorem eq_of_im {g : ℕ} (h τ Hm A B : Matrix (Fin g) (Fin g) ℂ) (hA : h * A = 1) (hB : h * B = τ)
    (h1 : ∀ a b, ((Aᵀ * Hm * A.map (starRingEnd ℂ)) a b).im = 0)
    (h2 : ∀ a b, ((Aᵀ * Hm * B.map (starRingEnd ℂ)) a b).im = -(1 : Matrix (Fin g) (Fin g) ℝ) a b) :
    Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧
      Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  have hA' : A * h = 1 := mul_eq_one_comm.mp hA
  have hB' : B = A * τ := by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM
  have hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [hB', Matrix.map_mul, hM]; simp only [Matrix.mul_assoc]
  have hMY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext a b
    have := h2 a b
    rw [hMB, Matrix.mul_apply, Complex.im_sum] at this
    rw [Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [h1 a c]
  have hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re := Matrix.inv_eq_left_inv hMY
  have hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M := by
    ext a b
    apply Complex.ext <;> simp [h1 a b]
  have hH : Hm = hᵀ * M * h.map (starRingEnd ℂ) := by
    have e1 : hᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]
    have e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hA']; simp
    calc Hm = (hᵀ * Aᵀ) * Hm * (A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ)) := by
          rw [e1, e2]; simp
      _ = _ := by rw [hM]; simp only [Matrix.mul_assoc]
  refine ⟨by rw [hinv, hMre]; exact hH, ?_⟩
  have hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1 := by
    have e := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_one] at e
    have e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ) := by
      conv_lhs => rw [← hMre]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [e']; exact_mod_cast e
  have hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det :=
    (RingHom.map_det (starRingEnd ℂ) h).symm
  rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  have := Complex.mul_conj' h.det
  push_cast
  linear_combination (h.det * starRingEnd ℂ h.det) * hd + this

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → Fin g → ℂ) (a b : Fin g) :
    ((Matrix.of u)ᵀᵀ * Hm * ((Matrix.of v)ᵀ).map (starRingEnd ℂ)) a b = hermForm Hm (u a) (v b) := by
  rw [Matrix.mul_assoc]
  rfl

theorem herm_eq_of_normalised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (P : D.La →+ (Fin g → ℂ)) (h τ Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) → IsPeriod D ty P → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → τ ∈ SiegelH (Fin g) → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧ Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  intro E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH
  refine eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ
    (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_
  · ext i k
    have := congrFun (hn k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  · ext i k
    have := congrFun (hn k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd]
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all [eq_comm]

end GlobalTheory.RiemannForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoord_exists_unique_up_to_unit_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)), IsIntegrallyClosed R → ∀ χ, (∃ r, PsiCoord Dg.toPre χ r ∧ r ≠ 0 ∧ (χ ≠ 0 → r ∈ maximalIdeal R) ∧ (χ = 0 → IsUnit r)) ∧ (∀ r r', PsiCoord Dg.toPre χ r → PsiCoord Dg.toPre χ r' → ∃ u : Rˣ, r' = u * r) ∧ ∀ (W : Set (Sp R)) (𝔭 : PrimeSpectrum R), IsOpen W → 𝔭 ∈ W → PsiUnitOn Dg.toPre χ W → ∀ r, PsiCoord Dg.toPre χ r → r ∉ 𝔭.asIdeal := by
  first | exact @GlobalTheory.PsiCoordLocal.main | exact GlobalTheory.PsiCoordLocal.main | (intros; apply GlobalTheory.PsiCoordLocal.main <;> assumption)
end

