import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Glue

theorem app_map {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U V : Y.Opens} (i : U ⟶ V) (a : Γ(Y, V)) :
    (p.app U).hom ((Y.presheaf.map i.op).hom a) =
      (Z.presheaf.map (homOfLE (p.preimage_mono i.le)).op).hom ((p.app V).hom a) := by
  rw [← CommRingCat.comp_apply, p.naturality, CommRingCat.comp_apply]
  rfl

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (x : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom x) =
      (X.presheaf.map (homOfLE (j.le.trans i.le)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem le_iSup_affine (Y : Scheme.{0}) (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

theorem le_iSup_preimage_affine {Y Z : Scheme.{0}} (p : Z ⟶ Y) (V : Y.Opens) :
    p ⁻¹ᵁ V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, p ⁻¹ᵁ U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

end GlobalTheory.Mum.Glue

namespace GlobalTheory.Mum

theorem app_injective_and_descent_of_affineOpens : ∀ (Y Z : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, IsAffineOpen V → (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom)) → ∀ V : Y.Opens, (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom) := by
  intro Y Z p H
  have inj : ∀ W : Y.Opens, Function.Injective (p.app W).hom := by
    intro W a b hab
    refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ W} ↦ U.1.1) W
      (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y W) a b fun U ↦ ?_
    apply (H U.1.1 U.1.2).1
    show (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom a) =
      (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom b)
    rw [Glue.app_map, Glue.app_map, hab]
  intro V
  refine ⟨inj V, fun f hf ↦ ?_⟩
  have hV : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    show (pullback.snd p p ≫ p) ⁻¹ᵁ V = (pullback.fst p p ≫ p) ⁻¹ᵁ V
    rw [pullback.condition]
  have hf' := hf hV
  have hU : ∀ U : {U : Y.affineOpens // U.1 ≤ V}, ∃ g : Γ(Y, U.1.1), (p.app U.1.1).hom g =
      (Z.presheaf.map (homOfLE (p.preimage_mono U.2)).op).hom f := by
    intro U
    apply (H U.1.1 U.1.2).2
    intro h'
    rw [Glue.app_map, hf', ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE]
  choose g hg using hU
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ U.1.1) V
    (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y V) g (by
      intro U U'
      apply inj
      show (p.app _).hom ((Y.presheaf.map _).hom (g U)) = (p.app _).hom ((Y.presheaf.map _).hom (g U'))
      rw [Glue.app_map, Glue.app_map, hg, hg, Glue.map_map, Glue.map_map])
  refine ⟨s, ?_⟩
  refine Z.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ p ⁻¹ᵁ U.1.1) (p ⁻¹ᵁ V)
    (fun U ↦ homOfLE (p.preimage_mono U.2)) (Glue.le_iSup_preimage_affine p V) _ _ fun U ↦ ?_
  have e := Glue.app_map p (homOfLE U.2) s
  have hsU : (Y.presheaf.map (homOfLE U.2).op).hom s = g U := hs U
  rw [hsU, hg] at e
  exact e.symm

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

theorem ahFactor_im_int_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := by
    haveI := q.isPrime
    haveI := p0.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime p0.asIdeal).symm)
  rw [this]
  exact hj

theorem ahFactor_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (v w : Fin g → ℂ) : w ⬝ᵥ Hm.mulVec (star v) = star (v ⬝ᵥ Hm.mulVec (star w)) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b, star_star]
  ring

theorem ahFactor_im_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  intro g A _ L u Hm χ hL hF l hl l' hl'
  obtain ⟨hH, hχ, hfac⟩ := hF
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart L hL (u.ex 0).left
  have hex : ∀ z ∈ u.Λ, u.ex z = u.ex 0 := fun z hz => by
    rw [(u.ker z).mpr hz, (u.ker 0).mpr (zero_mem _)]
  have hc : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := fun z hz => by rw [hex z hz]; exact hi
  have e1 := hfac ⟨l, hl⟩ i 0 (hc 0 (zero_mem _))
  have e2 := hfac ⟨l', hl'⟩ i l (hc l hl)
  have e3 := hfac ⟨l', hl'⟩ i 0 (hc 0 (zero_mem _))
  have e4 := hfac ⟨l, hl⟩ i l' (hc l' hl')
  have hne := u.fr_ne i (l + l') (hc _ (add_mem hl hl'))
  have hχ1 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
  have hχ2 : χ ⟨l', hl'⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l', hl'⟩
  have hsw := ahFactor_herm_swap hH l l'
  simp only [zero_add, zero_dotProduct, mul_zero] at e1 e3
  rw [e2] at e1
  rw [e4, add_comm l' l] at e3
  have key := e1.symm.trans e3
  set F := u.fr i (l + l')
  set H := l ⬝ᵥ Hm.mulVec (star l')
  set H' := l' ⬝ᵥ Hm.mulVec (star l')
  set H0 := l ⬝ᵥ Hm.mulVec (star l)
  set Hs := l' ⬝ᵥ Hm.mulVec (star l)
  set c1 := χ ⟨l, hl⟩
  set c2 := χ ⟨l', hl'⟩
  have key2 : (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) =
      (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0)) := by
    simp only [Complex.exp_add] at key ⊢
    linear_combination key
  have hnz : c1 * c2 * F ≠ 0 := mul_ne_zero (mul_ne_zero hχ1 hχ2) hne
  have key3 := mul_left_cancel₀ hnz key2
  have key4 : Complex.exp ((Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) -
      (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0))) = 1 := by
    rw [Complex.exp_sub, key3, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key4
  refine ⟨n, ?_⟩
  have hsc : H - Hs = 2 * (H.im : ℂ) * Complex.I := by
    rw [hsw]
    have h7 := Complex.sub_conj H
    push_cast at h7
    exact h7
  have h5 : ((H.im : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination hn - (Real.pi : ℂ) * hsc
  have h6 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right Complex.two_pi_I_ne_zero)
  exact_mod_cast h6

end GlobalTheory.TorusRM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.PolarDeg

theorem lin_coeff_eq {ι κ : Type} (s : Finset ι) (s' : Finset κ) (a : ι → ℝ) (e : ι → ℕ) (b : κ → ℝ) (e' : κ → ℕ)
    (h : ∀ t : ℝ, ∑ i ∈ s, a i * t ^ e i = ∑ j ∈ s', b j * t ^ e' j) :
    ∑ i ∈ s, (if e i = 1 then a i else 0) = ∑ j ∈ s', (if e' j = 1 then b j else 0) := by
  have hP : (∑ i ∈ s, Polynomial.C (a i) * Polynomial.X ^ e i) =
      ∑ j ∈ s', Polynomial.C (b j) * Polynomial.X ^ e' j := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact h t
  have := congrArg (fun p => Polynomial.coeff p 1) hP
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
  simpa [eq_comm] using this

theorem num_expand {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) (t : ℝ) :
    f (fun _ => x + t • y) =
      ∑ s : Finset (Fin (n + 1)), f (s.piecewise (fun _ => y) (fun _ => x)) * t ^ s.card := by
  have h1 : (fun _ : Fin (n + 1) => x + t • y) = (fun _ => t • y) + (fun _ => x) := by
    funext i; simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun _ : Fin (n + 1) => t • y) (fun _ => x) =
      s.piecewise (fun i => (fun _ : Fin (n + 1) => t) i • (s.piecewise (fun _ => y) (fun _ => x)) i)
        (s.piecewise (fun _ => y) (fun _ => x)) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h2, MultilinearMap.map_piecewise_smul, Finset.prod_const, smul_eq_mul, mul_comm]

theorem num_lin {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) :
    ∑ s : Finset (Fin (n + 1)), (if s.card = 1 then f (s.piecewise (fun _ => y) (fun _ => x)) else 0) =
      ((n : ℝ) + 1) * f (Fin.cons y fun _ => x) := by
  rw [← Finset.sum_filter]
  have hS : (Finset.univ.filter fun s : Finset (Fin (n + 1)) => s.card = 1) =
      Finset.univ.map ⟨fun i => {i}, Finset.singleton_injective⟩ := by
    ext s
    rw [Finset.mem_filter, Finset.mem_map, Finset.card_eq_one]
    simp only [Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor <;> rintro ⟨a, h⟩ <;> exact ⟨a, h.symm⟩
  rw [hS, Finset.sum_map]
  have h3 : ∀ i : Fin (n + 1), f (({i} : Finset (Fin (n + 1))).piecewise (fun _ => y) (fun _ => x)) =
      f (Fin.cons y fun _ => x) := by
    intro i
    rw [Finset.piecewise_singleton]
    have h4 : Function.update (fun _ : Fin (n + 1) => x) i y ∘ (Equiv.swap 0 i) =
        (Fin.cons y fun _ => x : Fin (n + 1) → V) := by
      rw [Function.update_comp_equiv]
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp [Function.update, Equiv.swap_apply_def]
    rw [← h4, hf]
  simp only [Function.Embedding.coeFn_mk, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.PolarDeg

namespace GlobalTheory.PolarDeg

open MvPolynomial in

theorem linRoot_add_smul {ι : Type} [Fintype ι] {N : ℕ} (u w : ι → Fin N → ℝ) (t : ℝ) :
    Formalism.DegreeFormula.linRoot (u + t • w) = C t * Formalism.DegreeFormula.linRoot w + Formalism.DegreeFormula.linRoot u := by
  simp only [Formalism.DegreeFormula.linRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, C_add, C_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

open MvPolynomial in

theorem arDeg_lin_mul_pow (D : D7) (Y : DV.ShimX D.what₂.Tau) (T : Real0 Y) (hT : TieDeg T) (B : ℝ) (hB : 2 ≤ B)
    (R : ℝ) (hR : Real.exp 2 ≤ R) (w u : Wt Y) :
    Y.arDeg (GlobalTheory.FlagAr.setB Y B) R (Formalism.DegreeFormula.linRoot w * Formalism.DegreeFormula.linRoot u ^ Formalism.MainNotions.WeightThresholdDefs.dimY Y) =
      ∑ c, (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := by
  set A := Y.arDeg (GlobalTheory.FlagAr.setB Y B) R with hA
  set lw := Formalism.DegreeFormula.linRoot w
  set lu := Formalism.DegreeFormula.linRoot u
  have hf : ∀ t : ℝ, A (Formalism.DegreeFormula.linRoot (u + t • w) ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) =
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m := by
    intro t
    rw [linRoot_add_smul, add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (C t * lw) ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m) * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : MvPolynomial _ ℝ) =
        (t ^ m * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : ℝ)) • (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m)) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow, C_mul, ← map_natCast (C : ℝ →+* MvPolynomial _ ℝ)]
      ring
    rw [h1, map_smul, smul_eq_mul]
    ring
  have hg : ∀ t : ℝ, ∑ c, T.fR B c (u + t • w) 0 R =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : T.L B c (u + t • w) + (0 : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phR R (u + t • w)) =
        (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) + t • (T.L B c w + (T.K B c).ar ((T.F c).phR R w)) := by
      simp only [map_add, map_smul, zero_smul, add_zero, smul_add]
      abel
    rw [Real0.fR, Calc.top, h2]
    exact num_expand (T.K B c).num (T.K B c).symm _ _ t
  have hfg : ∀ t : ℝ,
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [← hf, ← hg]
    exact hT B hB R hR (u + t • w)
  have hc := lin_coeff_eq _ _ _ (fun m => m) _ (fun p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) => p.2.card) hfg
  rw [Fintype.sum_prod_type] at hc
  simp only [Finset.sum_ite_eq', Finset.mem_range] at hc
  have hsum : ∀ c, (∑ s : Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)), if s.card = 1 then
      (T.K B c).num (s.piecewise (fun _ => T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        (fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u))) else 0) =
      ((Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1) * (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := fun c => by
    convert num_lin (T.K B c).num (T.K B c).symm _ _ using 5
  replace hc := hc.trans (Finset.sum_congr rfl fun c _ => hsum c)
  have hn1 : (0 : ℝ) < (Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1 := by positivity
  rw [if_pos (by omega), Nat.choose_one_right, pow_one, Nat.add_sub_cancel, ← Finset.mul_sum] at hc
  push_cast at hc
  exact mul_left_cancel₀ hn1.ne' hc

end GlobalTheory.PolarDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricPairMatrixHorizontalSingleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  first | exact @GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | exact GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | (intros; apply GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBis
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem Good.good_of_isPullback' {g : ℕ} {X Y X' Y' : Scheme.{0}} {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {h : Y' ⟶ Y} (sq : IsPullback k f' f h) (hf : Good g f) : Good g f' where
  proper := MorphismProperty.of_isPullback sq hf.proper
  smooth := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback sq hf.smooth
  conn := MorphismProperty.of_isPullback sq hf.conn

theorem HasRep.baseChange (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (h : S'' ⟶ S')
    (H : HasRep A g S') : HasRep A g S'' := by
  obtain ⟨B, b, P, hRep, hGood⟩ := H

  have sq := IsPullback.of_hasPullback b h
  refine ⟨pullback b h, pullback.snd b h, ev P (fst A (pullback b h)) (snd A (pullback b h) ≫ pullback.fst b h),
    GlobalTheory.T.rep_ev_of_isPullback S A B S' S'' (pullback b h) b P h _ _ hRep sq, ?_⟩

  exact Good.good_of_isPullback' (sq.map (Over.forget S)) hGood

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCoefficientComparisonCommPairPullback
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open Opposite
namespace GlobalTheory.Obs.BC

theorem tensPair_extMap_pairPull : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  intro R₀ R₁ _ _ _ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' _ _ w w' f₀ f₁ h₀ h₁ e p b
  have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (U : X₀.Opens) (V : Y₁.Opens) (k : V ≤ g ⁻¹ᵁ U) (k' : V ≤ g' ⁻¹ᵁ U),
      g.appLE U V k = g'.appLE U V k' := by
    rintro g _ rfl U V k k'; rfl
  change tensHom w' (unop ((pairFst f₀).obj p)) _ (extHom R₁ (coefHom (pairPull h₀) p) b) =
    GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop) (tensHom w (unop ((pairSnd f₀).obj p)) _ b)
  induction b using TensorProduct.induction_on with
  | zero => repeat erw [map_zero]
            all_goals exact rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]; exact rfl
  | tmul r x =>
    refine (congrArg (tensHom w' _ _) (Algebra.TensorProduct.map_tmul _ _ r x)).trans ?_
    refine (tensHom_tmul w' _ _ r _).trans ?_
    have h2 := congrArg (GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop))
      (tensHom_tmul w (unop ((pairSnd f₀).obj p)) ((isAffine_aff _).preimage pr) r x)
    refine Eq.trans ?_ h2.symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · exact ((semiHom_secPull h₁ (pairBCObj pr pr' e p.unop)).map_algebraMap r).symm
    · change (pr'.appLE _ _ _).hom ((f₀.appLE _ _ _).hom x) = (f₁.appLE _ _ _).hom ((pr.appLE _ _ _).hom x)
      have c1 := Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1 (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl
      have c2 := Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1 (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl
        (pairBCObj pr pr' e p.unop).2
      rw [key (pr' ≫ f₀) (f₁ ≫ pr) e.symm _ _ _ (by rw [e]; exact pr'.preimage_mono p.unop.2)] at c1
      exact (congrArg (fun t ↦ t.hom x) c1).trans (congrArg (fun t ↦ t.hom x) c2).symm

end GlobalTheory.Obs.BC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionBaseChangeKerMemMapAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  first | exact @GlobalTheory.closedImmersion_baseChange_ker_mem_map | exact GlobalTheory.closedImmersion_baseChange_ker_mem_map | (intros; apply GlobalTheory.closedImmersion_baseChange_ker_mem_map <;> assumption)
end

