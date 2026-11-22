import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoFT

theorem finiteType_affine {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  have h1 : (q.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  have h3 : (strV q W).FiniteType := by
    have : strV q W = (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl
    rw [this]
    exact h1.comp h2
  letI := (strV q W).toAlgebra
  exact RingHom.finiteType_algebraMap.1 h3

end GlobalTheory.CompanionTheory.GeoFT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegral
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTorus

theorem isAlgebraic_unit_inv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) : IsAlgebraic A ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Polynomial.C (⟨u, hu⟩ : A) * Polynomial.X - 1, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p => Polynomial.coeff p 0) h
    simp at h1
  · simp [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul]

theorem isAlgebraic_unit_zpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) (m : ℤ) : IsAlgebraic A ((u ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · have h : IsAlgebraic A (u : R) := isAlgebraic_algebraMap (⟨u, hu⟩ : A)
    simpa using h.pow n
  · simpa using (isAlgebraic_unit_inv A u hu).pow n

theorem isAlgebraic_tpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ}
    (t : Fin d → Rˣ) (m : Fin d → ℤ) :
    IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) (tpow t m) := by
  set A := Algebra.adjoin K (Set.range fun k => (t k : R))
  have hmem : ∀ k, (t k : R) ∈ A := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  have key : ∀ s : Finset (Fin d), IsAlgebraic A (((∏ k ∈ s, t k ^ m k : Rˣ)) : R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic A (1 : R))
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      exact (isAlgebraic_unit_zpow A (t a) (hmem a) (m a)).mul ih
  exact key Finset.univ

theorem isAlgebraic_of_integral_torusS : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  intro K R _ _ _ _ d t hint
  set A := Algebra.adjoin K (Set.range fun k => (t k : R)) with hA
  let S : Subalgebra A R := Subalgebra.algebraicClosure A R
  have hle : ∀ b : torusS K t Finset.univ, (b : R) ∈ S := by
    rintro ⟨b, hb⟩
    have : torusS K t Finset.univ ≤ S.restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨m, -, rfl⟩
      exact (Subalgebra.mem_algebraicClosure A R).2 (isAlgebraic_tpow t m)
    exact this hb
  let φ : torusS K t Finset.univ →+* S :=
    { toFun := fun b => ⟨b, hle b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨fun r => ?_⟩
  obtain ⟨p, hm, hp⟩ := hint r
  have hS : IsIntegral S r := by
    refine ⟨p.map φ, hm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact hS.isAlgebraic.restrictScalars A

end GlobalTheory.CompanionTheory.GeoTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlmostFinitelyGeneratedSerreClass
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.AlmostFinite

section Sub

variable {R : Type} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def AF (c : R) (N : Submodule R M) : Prop :=
  ∃ (n : ℕ) (G : Submodule R M), G.FG ∧ G ≤ N ∧ ∀ x ∈ N, c ^ n • x ∈ G

def AN (c : R) (A : Submodule R M) : Prop := ∀ N : Submodule R M, N ≤ A → AF c N

theorem AN.mono {c : R} {A B : Submodule R M} (h : AN c B) (hAB : A ≤ B) : AN c A :=
  fun N hN => h N (hN.trans hAB)

theorem an_bot (c : R) : AN c (⊥ : Submodule R M) := fun N hN =>
  ⟨0, ⊥, Submodule.fg_bot, bot_le, fun x hx => by
    have h := hN hx
    simp only [Submodule.mem_bot] at h
    simp [h]⟩

theorem AN.step {I : Ideal R} {c : R}
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {A : Submodule R M} {x : M} (hx : ∀ i ∈ I, i • x ∈ A) (hA : AN c A) :
    AN c (A ⊔ Submodule.span R {x}) := by
  intro N hN
  have key : ∃ (n : ℕ) (G : Submodule R M), G.FG ∧ G ≤ N ∧
      ∀ y ∈ N, ∃ g ∈ G, c ^ n • y - g ∈ A := by
    by_cases h : ∃ a₀ ∈ A, ∃ r₀ : R, r₀ ∉ I ∧ a₀ + r₀ • x ∈ N
    · obtain ⟨a₀, ha₀, r₀, hr₀, hy₀⟩ := h
      obtain ⟨n, hn⟩ := hc r₀ hr₀
      obtain ⟨u, hu, i, hi, hui⟩ := Submodule.mem_sup.1 hn
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hu
      refine ⟨n, Submodule.span R {a₀ + r₀ • x}, Submodule.fg_span_singleton _,
        (Submodule.span_singleton_le_iff_mem _ _).2 hy₀, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hN hy)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine ⟨(s * r) • (a₀ + r₀ • x),
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      have e : c ^ n • (a + r • x) - (s * r) • (a₀ + r₀ • x)
          = c ^ n • a + r • (i • x) - (s * r) • a₀ := by
        rw [← hui]; module
      rw [e]
      exact A.sub_mem (A.add_mem (A.smul_mem _ ha) (A.smul_mem _ (hx i hi))) (A.smul_mem _ ha₀)
    · refine ⟨0, ⊥, Submodule.fg_bot, bot_le, fun y hy => ⟨0, Submodule.zero_mem _, ?_⟩⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hN hy)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
      have hr : r ∈ I := by
        by_contra hr
        exact h ⟨a, ha, r, hr, hy⟩
      simpa using A.add_mem ha (hx r hr)
  obtain ⟨n, G, hG, hGN, hy⟩ := key
  obtain ⟨m, G₂, hG₂, hG₂le, hm⟩ := hA (N ⊓ A) inf_le_right
  refine ⟨m + n, G ⊔ G₂, hG.sup hG₂, sup_le hGN (hG₂le.trans inf_le_left), fun y hyN => ?_⟩
  obtain ⟨g, hg, hgA⟩ := hy y hyN
  have h1 : c ^ n • y - g ∈ N ⊓ A := ⟨N.sub_mem (N.smul_mem _ hyN) (hGN hg), hgA⟩
  have h2 := hm _ h1
  have e : c ^ (m + n) • y = c ^ m • g + c ^ m • (c ^ n • y - g) := by
    rw [pow_add, mul_smul, smul_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (G.smul_mem _ hg)) (Submodule.mem_sup_right h2)

theorem AN.finset {I : Ideal R} {c : R}
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {A : Submodule R M} (hA : AN c A) (T : Finset M) (hT : ∀ t ∈ T, ∀ i ∈ I, i • t ∈ A) :
    AN c (A ⊔ Submodule.span R (T : Set M)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hA
  | insert a s _ ih =>
    have h := AN.step hc (A := A ⊔ Submodule.span R (s : Set M)) (x := a)
      (fun i hi => Submodule.mem_sup_left (hT a (Finset.mem_insert_self _ _) i hi))
      (ih fun t ht => hT t (Finset.mem_insert_of_mem ht))
    refine h.mono ?_
    rw [Finset.coe_insert, Submodule.span_insert]
    exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_right))

theorem AN.of_fg {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {F : Submodule R M} (hF : F.FG) : AN c F := by
  have main : ∀ d j : ℕ, I ^ (j + d) = ⊥ → AN c (I ^ j • F) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [add_zero] at hj
      rw [hj, Submodule.bot_smul]
      exact an_bot c
    | succ d ih =>
      intro j hj
      have hA : AN c (I ^ (j + 1) • F) := ih (j + 1) (by rw [← hj]; congr 1; omega)
      obtain ⟨T, hT⟩ : (I ^ j • F).FG := Submodule.FG.smul (hI.pow) hF
      refine (AN.finset hc hA T fun t ht i hi => ?_).mono ?_
      · have ht' : t ∈ I ^ j • F := hT ▸ Submodule.subset_span ht
        rw [pow_succ', mul_smul]
        exact Submodule.smul_mem_smul hi ht'
      · rw [hT]; exact le_sup_right
  obtain ⟨k, hk⟩ := hnil
  have := main k 0 (by simpa using hk)
  simpa using this

theorem af_of_afg {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hM : AFG c M) (N : Submodule R M) : AF c N := by
  obtain ⟨n, F, hF, hn⟩ := hM
  obtain ⟨m, G, hG, hGle, hm⟩ := AN.of_fg hI hnil hc hF (N ⊓ F) inf_le_right
  refine ⟨m + n, G, hG, hGle.trans inf_le_left, fun x hx => ?_⟩
  have h := hm _ (⟨N.smul_mem _ hx, hn x⟩ : c ^ n • x ∈ N ⊓ F)
  rwa [← mul_smul, ← pow_add] at h

theorem exists_fg_map_eq {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (g : M →ₗ[R] M₂)
    {G : Submodule R M₂} (hG : G.FG) (hle : G ≤ LinearMap.range g) :
    ∃ G' : Submodule R M, G'.FG ∧ G'.map g = G := by
  classical
  obtain ⟨s, rfl⟩ := hG
  have h : (s : Set M₂) ⊆ g '' Set.univ := fun y hy => by
    simpa using hle (Submodule.subset_span hy)
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 h
  exact ⟨Submodule.span R (s' : Set M), ⟨s', rfl⟩, by rw [Submodule.map_span]; simp⟩

theorem afg_mid {I : Ideal R} {c : R} (hI : I.FG) (hnil : IsNilpotent I)
    (hc : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (h₁ : AFG c M₁) (h₃ : AFG c M₃) : AFG c M₂ := by
  obtain ⟨a, G₃, hG₃, hG₃le, ha⟩ := af_of_afg hI hnil hc h₃ (LinearMap.range g)
  obtain ⟨G', hG', rfl⟩ := exists_fg_map_eq g hG₃ hG₃le
  obtain ⟨b, N₁, hN₁, hb⟩ := h₁
  refine ⟨b + a, G' ⊔ N₁.map f, hG'.sup (hN₁.map f), fun x => ?_⟩
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_map).1 (ha (g x) ⟨x, rfl⟩)
  obtain ⟨z, hz⟩ := (hfg (c ^ a • x - y)).1 (by rw [map_sub, map_smul, hyx, sub_self])
  have e : c ^ (b + a) • x = c ^ b • y + f (c ^ b • z) := by
    rw [map_smul, hz, pow_add, mul_smul, smul_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (G'.smul_mem _ hy))
    (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hb z)))

end Sub

theorem serre_afg : ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    ∃ 𝒮 : Serre.{1} R, ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ AFG c M := by
  intro R _ I c hI hnil _ _ hc
  refine ⟨⟨fun M _ _ => AFG c M, fun M _ _ _ => ⟨0, ⊥, Submodule.fg_bot, fun x => ?_⟩,
    fun M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ => afg_mid hI hnil hc f g hfg h₁ h₃⟩,
    fun M _ _ => Iff.rfl⟩
  simp [Subsingleton.elim x 0]

end GlobalTheory.CompanionTheory.AlmostFinite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem evV_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  intro K _ X N i hi g e hg he
  have hU : IsAffineOpen (Proj.basicOpen (grK K N) g) := Proj.isAffineOpen_basicOpen (grK K N) g hg he
  have hiso : IsIso (Proj.awayToSection (grK K N) g) := (Proj.basicOpenIsoAway (grK K N) g hg he).isIso_hom
  have h1 : Function.Surjective (Proj.awayToSection (grK K N) g).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grK K N) g)).2
  have h2 : Function.Surjective (i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective _ hU
  exact h2.comp h1

end GlobalTheory.CompanionTheory.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZero
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem preimage_basicOpen_nonempty_of_mk_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ PSpace K N) (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hne : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  by_contra hE
  apply hne
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  have hg' : g ∈ grK K N (e • 1) := by simpa using hg
  refine ⟨e, hg', fun j => ?_⟩
  have hy : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) e g hg' =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
  rw [hy, ← basicOpen_eq_bot_iff]
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hg he
  have h2 : X.basicOpen (evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) =
      i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
        (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) := by
    rw [Scheme.preimage_basicOpen]
    simp only [evV, Scheme.Hom.appLE_eq_app]
    rfl
  rw [h2, hb, eq_bot_iff]
  intro x hx
  exact hE ⟨x, hx.2⟩

end GlobalTheory.CompanionTheory.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCover

theorem X_mem_of_finite {K : Type} [Field K] {n m : ℕ}
    (I P : Ideal (MvPolynomial (Fin n) K)) [hPp : P.IsPrime] (hIP : I ≤ P)
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (y : Fin m → MvPolynomial (Fin n) K) (hy : ∀ k, y k ∈ P)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))
    (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) K) ∈ P := by
  classical
  by_contra hj
  let φ : (MvPolynomial (Fin n) K ⧸ I) →+* (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.factor hIP
  have hφ : ∀ g, φ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk P g := fun g => rfl
  let Q : Ideal (MvPolynomial (Fin n) K ⧸ I) := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  have hc0 : ∀ r ∈ Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)),
      ∃ c : K, φ r = Ideal.Quotient.mk P (MvPolynomial.C c) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨0, by rw [hφ, map_zero, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hy k)⟩
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [map_add, hc, hd, map_add, map_add]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by rw [map_mul, hc, hd, map_mul, map_mul]⟩
  have h1 : (1 : MvPolynomial (Fin n) K ⧸ P) ≠ 0 := by
    intro h
    have : (1 : MvPolynomial (Fin n) K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h)
    exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hmax : (Q.comap (algebraMap (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => h1 ?_, fun J x hle hx hxJ => ?_⟩
    · have : φ 1 = 0 := by simpa [Q, RingHom.mem_ker, Ideal.mem_comap] using h
      simpa using this
    · obtain ⟨c, hc⟩ := hc0 x.1 x.2
      have hc' : c ≠ 0 := by
        rintro rfl
        apply hx
        rw [Ideal.mem_comap]
        change φ x.1 = 0
        rw [hc, map_zero, map_zero]
      have hm : x * algebraMap K _ c⁻¹ - 1 ∈ J := by
        apply hle
        rw [Ideal.mem_comap]
        change φ (x.1 * algebraMap K _ c⁻¹ - 1) = 0
        rw [map_sub, map_mul, hc, map_one]
        change _ * Ideal.Quotient.mk P (MvPolynomial.C c⁻¹) - 1 = 0
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc', map_one, map_one, sub_self]
      have := J.sub_mem (J.mul_mem_right (algebraMap K _ c⁻¹) hxJ) hm
      simpa using this
  have hQ : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (R := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) Q hmax
  have hjQ : Ideal.Quotient.mk I (MvPolynomial.X j) ∉ Q := fun h =>
    hj (Ideal.Quotient.eq_zero_iff_mem.1 ((hφ _).symm.trans (RingHom.mem_ker.1 h)))
  obtain ⟨a, b, hb, hab⟩ := hQ.exists_inv hjQ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h2 : Ideal.Quotient.mk P (g * MvPolynomial.X j - 1) = 0 := by
    have := congrArg φ hab
    rw [map_add, map_mul, hφ, hφ, show φ b = 0 from hb, add_zero, map_one] at this
    rw [map_sub, map_mul, this, map_one, sub_self]
  have h3 : MvPolynomial.homogeneousComponent 0 (g * MvPolynomial.X j - 1) ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact hP 0 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have h4 : MvPolynomial.coeff 0 (g * MvPolynomial.X j - 1) = -1 := by
    have : MvPolynomial.constantCoeff (g * MvPolynomial.X j - 1) = -1 := by simp
    rwa [MvPolynomial.constantCoeff_eq] at this
  rw [MvPolynomial.homogeneousComponent_zero, h4, map_neg, map_one] at h3
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem h3))

theorem mem_of_evV_eq_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (p : X)
    (j : Fin (N + 1)) (hj : i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (d • 1))
    (h : evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    f ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
  by_contra hfP
  have hf' : f * MvPolynomial.X j ∈ grK K N (d + 1) := by
    have := SetLike.mul_mem_graded hf (xv_mem K N j)
    simpa using this
  have e : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by
      change MvPolynomial.X j ^ (d + 1) * f = MvPolynomial.X j ^ d * (f * MvPolynomial.X j)
      ring))
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hf' (Nat.succ_pos d)
  have hx : i p ∈ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := by
    erw [hb]
    refine ⟨hj, fun hm => ?_⟩
    exact ((i p : ProjectiveSpectrum (grK K N)).isPrime.mem_or_mem hm).elim hfP hj
  have hp : p ∈ i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := hx
  rw [Scheme.preimage_basicOpen, ← e] at hp
  have h0 : i.app _ (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  rw [h0, Scheme.basicOpen_zero] at hp
  exact hp

theorem iSup_preimage_eq_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  intro K _ X N i m e _ y _ hfin
  rw [_root_.eq_top_iff]
  intro p _
  by_contra hcon
  obtain ⟨j, hj⟩ : ∃ j, i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
    have : i p ∈ (⨆ j : Fin (N + 1), Proj.basicOpen (grK K N) (MvPolynomial.X j)) := by
      erw [GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hy : ∀ k, y k ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    intro k
    by_contra hk
    apply hcon
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, hk⟩
  have hle : homIdeal i ≤ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    rw [homIdeal, Ideal.span_le]
    rintro f ⟨d, hf, hv⟩
    exact mem_of_evV_eq_zero i p j hj hf (hv j)
  haveI : (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal.IsPrime :=
    (i p : ProjectiveSpectrum (grK K N)).isPrime
  exact hj (X_mem_of_finite _ _ hle
    (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).isHomogeneous y hy hfin j)

end GlobalTheory.CompanionTheory.GeoCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentPropertiesStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_idempotent_properties : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.zIdemFacts | exact GlobalTheory.CompanionTheory.TyFin.zIdemFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.zIdemFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUniqueStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChangeStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_forms_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) → ∀ a : ℕ, IsBaseChange (Aa C) (psi C θ hθ a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantsFiniteOfSmoothLeviStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariants_finite_of_smooth_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | exact GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd <;> assumption)
end

