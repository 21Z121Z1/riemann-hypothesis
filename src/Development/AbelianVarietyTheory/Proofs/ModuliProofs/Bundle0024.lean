import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_apply_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by
  classical
  have := Fintype.ofFinite G
  set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hmap : P.map x = P.map y := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hinvP]
  have hb : P.eval b = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have h0 : (P.map y).eval (y b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  rw [← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd] at h0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0
  obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨g, sub_eq_zero.mp hg⟩

theorem exists_smul_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) : ∃ g : G, ∀ b, y b = x (g • b) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc using hne
  have := Fintype.ofFinite G
  let e := Fintype.equivFin G
  let p : Polynomial B := ∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)
  have hcoef : ∀ g, p.coeff (e g) = c g := by
    intro g
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm))
      (by simp), if_pos rfl]
  have hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) →
      Polynomial.mapRingHom x q = Polynomial.mapRingHom y q := by
    intro q hq
    ext n
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hq]
  obtain ⟨g, hg⟩ := exists_smul_apply_eq_of_eq_on_invariants (G := G)
    (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p
  have hgc := congrArg (fun q => q.coeff (e g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc
  exact hc g hgc

theorem exists_aut_of_comp_eq_of_invariant {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).hom := by
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  have hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W
    rw [← hxy]
    exact hx
  have key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W),
      f.appLE W ⊤ h1 = f'.appLE W ⊤ h2 := by
    rintro f f' rfl h1 h2
    rfl
  have hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) →
      (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s := by
    intro s hs
    have hinv' : IsInvariantSection ρ _ s := by
      intro g
      refine ⟨hU g, ?_⟩
      have := hs g⁻¹
      rw [hact] at this
      simpa only [inv_inv] using this
    obtain ⟨t, rfl⟩ := hinv s hinv'
    have e1 := Scheme.Hom.comp_appLE x π W ⊤ hx
    have e2 := Scheme.Hom.comp_appLE y π W ⊤ hy
    have := congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)
    rw [e1, e2] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree
  refine ⟨g⁻¹, ?_⟩
  have h' : ⊤ ≤ (x ≫ (ρ g⁻¹).hom) ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).hom ⁻¹ᵁ π ⁻¹ᵁ W)
    exact hx.trans (x.preimage_mono (hU g⁻¹))
  have heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ W) ⊤ h' := by
    ext s
    rw [← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).hom _ _ _ (hU g⁻¹) hx]
    rw [hg s, hact]
    rfl
  have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).hom) hA (isAffineOpen_top T) h'
  rw [heq] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  exact (cancel_epi _).1 (h1.symm.trans h2)

theorem isIntegralHom_of_invariant {G : Type*} [Group G] [Finite G] {X X' : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) : IsIntegralHom π := by
  rw [isIntegralHom_iff]
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  classical
  have := Fintype.ofFinite G
  intro s
  rcases subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt
  · rw [Subsingleton.elim s 0]
    exact RingHom.isIntegralElem_zero _
  set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hlift : P ∈ Polynomial.lifts (π.app W).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hinv W hW
    intro g
    refine ⟨hU g, ?_⟩
    have := congrArg (fun q => q.coeff n) (hinvP g⁻¹)
    simp only [Polynomial.coeff_smul] at this
    rw [hact] at this
    simpa only [inv_inv] using this
  have hmonic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

theorem quotient_isIntegral_surjective_orbits :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsIntegralHom π ∧ Surjective π ∧ (∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x) ∧ (∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).hom) ∧ ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
  intro Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩
  have hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
    intro W _ s hs
    apply (hV W).2 s
    intro g h
    obtain ⟨h', e⟩ := hs g
    exact e
  have hInt : IsIntegralHom π := isIntegralHom_of_invariant ρ π hπ hinvAll
  have hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π →
      ∃ g, y = x ≫ (ρ g).hom := by
    intro k _ x y hxy
    let p₀ : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial
    refine exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_
    intro p _
    have hp : p = p₀ := Subsingleton.elim _ _
    subst hp
    exact hmem
  have hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x := by
    intro x y hxy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π =
        (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := hfield ((pullback π π).residueField z) _ _ hab
    refine ⟨g, ?_⟩
    let s : Spec ((pullback π π).residueField z) := ⟨⊥, Ideal.isPrime_bot⟩
    have ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x := by
      show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x
      rw [Scheme.fromSpecResidueField_apply]
      exact hz1
    have hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y := by
      show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y
      rw [Scheme.fromSpecResidueField_apply]
      exact hz2
    rw [← hb, hg, ← ha]
    rfl
  have hsurj : Surjective π := by
    rw [surjective_iff]
    intro y
    obtain ⟨W, hW, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
    have heq := IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl
    have hmem' : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hmem
    obtain ⟨p, rfl⟩ := hmem'
    have hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hInt.isIntegral_app W hW
    have hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact (hV W).1
    obtain ⟨q, hq⟩ := hint.comap_surjective hinj p
    refine ⟨hA.fromSpec q, ?_⟩
    have := congrArg (fun f => f q) heq
    rw [← hq]
    exact this.symm
  have hopen : ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
    intro U hU
    have hcl : IsClosed (π '' (U : Set X)ᶜ) := π.isClosedMap _ U.isOpen.isClosed_compl
    refine ⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩
    ext x
    show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · rintro hx ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := hpts x y hxy.symm
      apply hy
      have hx' : x ∈ (ρ g).hom ⁻¹ᵁ U := by
        rw [hU g]
        exact hx
      exact hx'
  exact ⟨hInt, hsurj, hpts, hfield, hopen⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSqAddSubDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SquareDensity

theorem exists_sq_add_sub_dvd {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ w : R, x ∣ w ∧ x ^ n ∣ w ^ 2 + w - x := by
  induction n with
  | zero => exact ⟨0, dvd_zero _, by simp⟩
  | succ n ih =>
    obtain ⟨w, ⟨c, hc⟩, hw⟩ := ih
    refine ⟨x - w ^ 2, ⟨1 - c * w, by rw [hc]; ring⟩, ?_⟩
    have h : (x - w ^ 2) ^ 2 + (x - w ^ 2) - x = (w ^ 2 + w - x) * (x * (c * w - c - 1)) := by
      have : x * (c * w - c - 1) = w ^ 2 - w - x := by rw [hc]; ring
      rw [this]; ring
    rw [h, pow_succ]
    exact mul_dvd_mul hw (dvd_mul_right _ _)

theorem dvd_aeval_sub_aeval {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have := dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem eval_aeval {K σ : Type*} [CommRing K] (Φ : MvPolynomial σ K) (a : σ → Polynomial K)
    (t : K) :
    (MvPolynomial.aeval a Φ).eval t = MvPolynomial.eval (fun i => (a i).eval t) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_zero_of_sq {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by
  set x : Polynomial (Polynomial ℤ) :=
    Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx
  obtain ⟨w, -, hw⟩ := exists_sq_add_sub_dvd x (d + 1)
  set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy
  obtain ⟨Φ, hd, hΦ⟩ := hΨ (max F.natDegree (y ^ 2).natDegree + 1)
  set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha
  set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb
  have hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) +
      Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X := by
    intro i
    have h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4 := rfl
    simp only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_one]
    split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring
  have hb0 : MvPolynomial.aeval b Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K))
      Int.cast_injective fun k => ?_
    show (MvPolynomial.aeval b Φ).eval (k : K) = 0
    rw [eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]
    · congr 2
      funext i
      simp only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      exact Polynomial.eval_intCast_map (Int.castRingHom K) _ k
    · exact lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _))
        (Nat.lt_succ_self _)
  have hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ := by
    rw [← sub_zero (MvPolynomial.aeval a Φ), ← hb0]
    apply dvd_aeval_sub_aeval
    intro i
    have h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2 := by
      have h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4) := by rw [hy]; ring
      rw [h2, map_pow]
      exact ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _
    have h3 := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i
    have h4 := Polynomial.map_dvd (Int.castRingHom K) h3
    simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub,
      Polynomial.map_sub] using h4
  have hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1 := by
    refine MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_
    rw [hai]
    compute_degree
  have ha0 : MvPolynomial.aeval a Φ = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [Polynomial.natDegree_X_pow]; omega)
  have h := eval_aeval Φ a (1 / 4)
  rw [ha0, Polynomial.eval_zero] at h
  rw [hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]
  congr 2
  funext i
  rw [hai]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coeff_sub, Int.cast_sub]
  ring

theorem eq_sum_monomial (F : Polynomial ℤ) (r : ℕ) (h : F.natDegree < r) :
    F = ∑ i : Fin r, Polynomial.monomial (i : ℕ) (F.coeff i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i)) r]
  exact F.as_sum_range' r h

theorem exists_det_polynomial {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    ∃ Φ : MvPolynomial (Fin r) K, Φ.IsHomogeneous m ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        φ (Polynomial.aeval U F).det =
          MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ := by
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K) := fun j k =>
    ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i
  have hM : ∀ j k, (M j k).IsHomogeneous 1 := fun j k =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _
  refine ⟨M.det, ?_, fun F hF => ?_⟩
  · rw [Matrix.det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
      fun i _ => hM _ _
    have h2 := h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)
    simpa using h2
  · rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext j k
    rw [Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range
      (fun i => F.coeff i • U ^ i) r]
    change φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _
      (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)
    rw [Matrix.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]

end SquareDensity

theorem sq_eq_det_aeval_of_sq : ∀ (l : ℕ) [Fact l.Prime] (m g : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (D : Polynomial ℤ → ℚ), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → (∀ G, ((D (G ^ 2) : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])) → (∀ F H, Polynomial.aeval U H = 0 → D (F + H) = D F) → ∀ F, ((D F ^ 2 : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m g U D hD hsq _ F
  refine sub_eq_zero.1 (SquareDensity.eq_zero_of_sq
    (fun F => ((D F ^ 2 : ℚ) : ℚ_[l]) - ((Polynomial.aeval U F).det : ℤ_[l]))
    (max (2 * g) m) (fun r => ?_) (fun G => ?_) F)
  · obtain ⟨Φ, hΦ, hDΦ⟩ := hD r
    obtain ⟨Θ, hΘ, hdet⟩ := SquareDensity.exists_det_polynomial (PadicInt.Coe.ringHom (p := l)) U r
    refine ⟨(MvPolynomial.map (algebraMap ℚ ℚ_[l]) Φ) ^ 2 - Θ, ?_, fun F hF => ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ?_ hΘ.totalDegree_le)
      have := ((hΦ.map (algebraMap ℚ ℚ_[l])).pow 2).totalDegree_le
      rwa [mul_comm] at this
    · rw [map_sub, map_pow, ← hdet F hF, Rat.cast_pow]
      congr 2
      have h1 := hDΦ fun i => F.coeff i
      rw [← SquareDensity.eq_sum_monomial F r hF] at h1
      rw [h1, MvPolynomial.eval_map]
      have h2 := MvPolynomial.eval₂_comp_left (algebraMap ℚ ℚ_[l]) (RingHom.id ℚ)
        (fun i : Fin r => ((F.coeff i : ℤ) : ℚ)) Φ
      simpa [Function.comp_def] using h2
  · simp only [map_pow, Matrix.det_pow, Rat.cast_pow, hsq G, PadicInt.coe_pow, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelianOfAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionFinite

theorem finite_torsion_semiAbelian_of_abelian :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} := by
  intro hB k _ _ G _ hG n hn
  haveI := hG.comm
  let t : Sp k ⟶ Sp k := 𝟙 _
  have h := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hB).1 k
    ((Over.pullback t).obj G) (hG.fibres k t) n hn
  have hp := isGrpPullback_pullback G t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom t = y.left ≫ pullback.fst G.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ G // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory.TorsionFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_stalk_Sp (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (y : Sp A) :
    IsDomain ((Sp A).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp A).presheaf.stalk y) := by
  have hy : (y.asIdeal : Ideal A).IsPrime := y.isPrime
  let _ : Algebra A ((Sp A).presheaf.stalk y) := StructureSheaf.stalkAlgebra A y
  have : IsLocalization.AtPrime ((Sp A).presheaf.stalk y) (y.asIdeal : Ideal A) :=
    StructureSheaf.IsLocalization.to_stalk A y
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (B := A) (y.asIdeal : Ideal A)
    ((Sp A).presheaf.stalk y)

theorem isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, hN, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s

end GlobalTheory
end

