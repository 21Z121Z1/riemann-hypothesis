import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubspaceMobiusInverseCharpolyPrimaryEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.Primary

theorem finrank_comap_of_surjective {F V U : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup U] [Module F U] (π : V →ₗ[F] U) (hπ : Function.Surjective π)
    (A : Submodule F U) :
    Module.finrank F (A.comap π) = Module.finrank F (LinearMap.ker π) + Module.finrank F A := by
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (A.comap π))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hπ, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap π)).finrank_eq] at h
  omega

theorem additive_pow {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]} (hf : f.Monic)
    (j : ℕ) : s (f ^ j) = j * s f := by
  induction j with
  | zero =>
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    simpa using this
  | succ j ih => rw [pow_succ, hs _ _ (hf.pow j) hf, ih]; push_cast; ring

theorem additive_restrict {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s : F[X] → ℂ} (hs : IsAdditive s) {g : Module.End F V} {f : F[X]} {m : ℕ} (hf : f.Monic)
    (hi : Irreducible f) (hc : LinearMap.charpoly g = f ^ m) (A : Submodule F V) (hA : ∀ x ∈ A, g x ∈ A) :
    (f.natDegree : ℂ) * s (LinearMap.charpoly (g.restrict hA)) = (Module.finrank F A : ℂ) * s f := by
  have h1 : LinearMap.charpoly (g.restrict hA) ∣ f ^ m :=
    hc ▸ ⟨_, charpoly_eq_restrict_mul_mapQ A g hA⟩
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hi.prime m).1 h1
  have h2 : LinearMap.charpoly (g.restrict hA) = f ^ j :=
    eq_of_monic_of_associated (LinearMap.charpoly_monic _) (hf.pow j) hj
  have h3 := LinearMap.charpoly_natDegree (g.restrict hA)
  rw [h2, hf.natDegree_pow] at h3
  rw [h2, additive_pow hs hf, ← h3]
  push_cast; ring

theorem eq_top_of_nilpotent {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : Module.End F V)
    {m : ℕ} (hN : N ^ m = 0) (W : Submodule F V) (hW : ∀ x ∈ W, N x ∈ W)
    (h : ∀ v, ∃ w ∈ W, ∃ u, v = w + N u) : W = ⊤ := by
  have hp : ∀ (j : ℕ), ∀ x ∈ W, (N ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih => intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hW x hx)
  have key : ∀ (j : ℕ) (v : V), ∃ w ∈ W, ∃ u, v = w + (N ^ j) u := by
    intro j
    induction j with
    | zero => intro v; exact ⟨0, W.zero_mem, v, by simp⟩
    | succ j ih =>
      intro v
      obtain ⟨w, hw, u, rfl⟩ := ih v
      obtain ⟨w', hw', u', rfl⟩ := h u
      refine ⟨w + (N ^ j) w', W.add_mem hw (hp j w' hw'), u', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨w, hw, u, rfl⟩ := key m v
  simpa [hN] using hw

theorem aeval_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) : ∀ x ∈ W, aeval g p x ∈ W := by
  first
  | exact @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | (apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem ..)

theorem mem_image_of_mem_span {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (f : F[X]) {t : ℕ} (π : V →ₗ[F] (Fin t → AdjoinRoot f)) (hπ : ∀ v, π (g v) = AdjoinRoot.root f • π v)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (y : Fin t → AdjoinRoot f)
    (hy : y ∈ Submodule.span (AdjoinRoot f) (π '' W)) : ∃ w ∈ W, π w = y := by
  have key : ∀ (p : F[X]) (v : V), π (aeval g p v) = AdjoinRoot.mk f p • π v := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro v
      rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, algebraMap_smul]
      simp
    | add p q hp hq => intro v; simp [hp, hq, add_smul]
    | monomial n a h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h, hπ, map_mul (AdjoinRoot.mk f) _ X,
        AdjoinRoot.mk_X, smul_smul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, W.zero_mem, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', W.add_mem hw hw', map_add _ _ _⟩
  | smul k x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective k
    exact ⟨_, aeval_mem g W hW p w hw, key p w⟩

end GlobalTheory.CuspGL.Primary

namespace GlobalTheory.CuspGL

open Primary in

theorem psi_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  intro F _ _ V _ _ _ s hs g f m t hf hi hm hc ht
  classical
  haveI : Fact (Irreducible f) := ⟨hi⟩
  have he : 0 < f.natDegree := hi.natDegree_pos
  have he' : (f.natDegree : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  obtain ⟨t', π, hsurj, hπ, hker, ht'⟩ := GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' F V g f
  obtain rfl : t' = t := Nat.eq_of_mul_eq_mul_left he (ht'.symm.trans ht)
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hK : Module.finrank F (AdjoinRoot f) = f.natDegree := (AdjoinRoot.powerBasis hi.ne_zero).finrank
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree := by
    rw [← hK]; exact Module.natCard_eq_pow_finrank
  have hN : (aeval g f) ^ m = 0 := by rw [← map_pow, ← hc, LinearMap.aeval_self_charpoly]
  have nak : ∀ W : Submodule F V, (∀ x ∈ W, g x ∈ W) →
      Submodule.span (AdjoinRoot f) (π '' W) = ⊤ → W = ⊤ := by
    intro W hW h
    refine eq_top_of_nilpotent (aeval g f) hN W (aeval_mem g W hW f) fun v => ?_
    obtain ⟨w, hw, hw'⟩ := mem_image_of_mem_span g f π hπ W hW (π v) (h ▸ Submodule.mem_top)
    have : v - w ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_sub, hw', sub_self]
    rw [hker] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨w, hw, u, by rw [hu]; abel⟩
  have htpos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with rfl | h
    · exfalso
      have h1 := nak ⊥ (by simp) (Subsingleton.elim _ _)
      have h2 := LinearMap.charpoly_natDegree g
      rw [hc, hf.natDegree_pow, ← finrank_top, ← h1, finrank_bot] at h2
      exact (Nat.mul_pos hm he).ne' h2
    · exact h
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)) :=
    Finite.of_injective _ SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F V)
  letI := Fintype.ofFinite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f))
  let P : Submodule F V → ℂ := fun W => if h : ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h) else 0
  let Φ : Submodule F V → Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) :=
    fun W => Submodule.span (AdjoinRoot f) (π '' W)
  let G : Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) → ℂ :=
    fun B => ∑ W ∈ Finset.univ.filter (fun W => Φ W = B), P W
  have hrk : Module.finrank (AdjoinRoot f) (Fin t' → AdjoinRoot f) = t' := by simp
  have main := GlobalTheory.T.mobiusInversion_affine_finrank_subspaces (AdjoinRoot f) (Fin t' → AdjoinRoot f) G
    ((Module.finrank F (LinearMap.ker π) : ℂ) * s f / f.natDegree) (s f) (by rw [hrk]; exact htpos) (by
      intro A
      have hA : ∀ x ∈ (A.restrictScalars F).comap π, g x ∈ (A.restrictScalars F).comap π := by
        intro x hx
        rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
        rw [hπ]; exact A.smul_mem _ hx
      have hle : ∀ W, Φ W ≤ A ↔ W ≤ (A.restrictScalars F).comap π := fun W => by
        rw [Submodule.span_le, Set.image_subset_iff]; rfl
      have h1 := finsum_psi_le F V s _ g hA
      have h2 := additive_restrict hs hf hi hc _ hA
      rw [finrank_comap_of_surjective π hsurj] at h2
      have h3 : Module.finrank F (A.restrictScalars F) = f.natDegree * Module.finrank (AdjoinRoot f) A := by
        rw [← hK, Module.finrank_mul_finrank]; rfl
      rw [h3] at h2
      have h4 : ∑ᶠ B : {B // B ≤ A}, G B.1 =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        rw [finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ A)) (by simp) G,
          Finset.sum_fiberwise_eq_sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext W; simp [hle]
      have h5 : ∑ᶠ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        have : ∀ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) = P W.1 := fun W => by simp only [P]; rw [dif_pos W.2.2]
        rw [finsum_congr this, finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter
            (fun W => W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W)) (by simp) P]
        refine Finset.sum_subset (fun W => by simp; tauto) fun W hW hW' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'
        exact dif_neg fun h => hW' ⟨hW, h⟩
      rw [h4, ← h5, h1]
      push_cast at h2
      field_simp
      linear_combination h2)
  have hG : G ⊤ = psi s V g := by
    have htop : ∀ x ∈ (⊤ : Submodule F V), g x ∈ (⊤ : Submodule F V) := fun _ _ => trivial
    have h1 : G ⊤ = P ⊤ := by
      refine Finset.sum_eq_single_of_mem ⊤ ?_ fun W hW hW' => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Φ]
        rw [Submodule.top_coe, Set.image_univ, hsurj.range_eq, Submodule.span_univ]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
        exact dif_neg fun h => hW' (nak W h hW)
    rw [h1]
    simp only [P]
    rw [dif_pos htop, ← psi_conj F s _ _ Submodule.topEquiv]
    congr 1
  rw [← hG, main, hrk, hcard]
  simp only [Nat.cast_pow, ← pow_mul]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChart
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.SecGlue

namespace GlobalTheory.SecGlue.ChartIndep

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {f g : Sp S ⟶ Y}
    (e : f = g) (hf : f ⁻¹ᵁ V = ⊤) (hg : g ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hf x = chartHom V g hg x := by
  subst e; rfl

theorem chartHom_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (f : Sp S ⟶ Y) (hf : f ⁻¹ᵁ V = ⊤) (hgf : (spMap g ≫ f) ⁻¹ᵁ V = ⊤)
    (x : Γ(Y, V)) : chartHom V (spMap g ≫ f) hgf x = g (chartHom V f hf x) := by
  unfold chartHom
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f V ⊤ ⊤ hf.ge le_top]
  have h1 : Scheme.Hom.appLE (spMap g) ⊤ ⊤ le_top = (spMap g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  rw [h1]
  change ((Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
    ((Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (f.appLE V ⊤ hf.ge).hom)) x = _
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]
  rfl

theorem chartHom_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by
  unfold chartHom
  rw [← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]
  rfl

theorem lands_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) : f ⁻¹ᵁ V = ⊤ :=
  top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))

theorem comb_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (h : IsCombIn W u c w a) : IsCombIn V u c w a := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  refine ⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩
  rw [chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartHom_mono hWV (w i) (hw i)]

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)

noncomputable def locMap : Localization.Away s →+* Localization ((Submonoid.powers s).map q) :=
  IsLocalization.map (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ q (Submonoid.le_comap_map _)

theorem locMap_alg (x : S) :
    locMap q s (algebraMap S (Localization.Away s) x) =
      algebraMap T (Localization ((Submonoid.powers s).map q)) (q x) :=
  IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ x

theorem locMap_surj (hq : Function.Surjective q) : Function.Surjective (locMap q s) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers s) (Localization.Away s)
    (Localization ((Submonoid.powers s).map q)) hq

theorem locMap_ker (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by
  have hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hk] at this
    exact (Submodule.mem_bot S).mp this

  have hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s),
      k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m := by
    intro x hx
    obtain ⟨⟨k, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
    rw [RingHom.mem_ker] at hx
    simp only [locMap] at hx
    rw [IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s)
      (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m', hm'⟩, hm'k⟩ := hx
    obtain ⟨m'', hm'', rfl⟩ := Submonoid.mem_map.mp hm'
    refine ⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_mul]; exact hm'k
    · simp only
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      ring_nf
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨k, m, hk1, rfl⟩ := hform x hx
  obtain ⟨k', m', hk2, rfl⟩ := hform y hy
  rw [← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]
  exact Submodule.zero_mem _

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

theorem lands_loc {Y : Scheme.{0}} (W : Y.Opens) {S : Type} [CommRing S] (s : S) (f : Sp S ⟶ Y)
    (hs : ∀ p : Sp S, s ∉ p.asIdeal → p ∈ f ⁻¹ᵁ W) :
    (spMap (algebraMap S (Localization.Away s)) ≫ f) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_preimage]
  apply hs
  intro hx
  change s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx
  rw [Ideal.mem_comap] at hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))

theorem eq_zero_of_loc {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by
  by_contra hD
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S S D)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : S) ∈ I := hI ▸ Submodule.mem_top
    simp [I] at this
    exact hD this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsD⟩ := h p hp
  obtain ⟨⟨m, hm⟩, hmD⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD
  obtain ⟨n, rfl⟩ := hm
  have : s ^ n ∈ I := by simp [I]; exact hmD
  exact hs (hp.isPrime.mem_of_pow_mem n (hIp this))

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue

open ChartIndep

theorem isCombIn_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  intro Y V V' hV _hV' S T _ _ q hq hk ι _ u c w a hw hcomb hu'

  have hqc : spMap q ≫ c = spMap q ≫ u := by
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S T q ι u c w a hcomb
    refine GlobalTheory.T.isAffineCombinationInChart_unique Y V hV T ι (spMap q ≫ u) _ _ (fun i => spMap q ≫ w i) (fun i => q (a i)) h1 ?_
    obtain ⟨hu1, _, hw1, _⟩ := h1
    refine ⟨hu1, hu1, hw1, fun x => ?_⟩
    have h0 : ∀ i, chartHom V (spMap q ≫ w i) (hw1 i) x - chartHom V (spMap q ≫ u) hu1 x = 0 :=
      fun i => by rw [chartHom_congr V (hw i) (hw1 i) hu1 x, sub_self]
    simp [h0]

  have hc' : c ⁻¹ᵁ V' = ⊤ := by rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm V']; exact hu'
  have hw' : ∀ i, w i ⁻¹ᵁ V' = ⊤ := fun i => by
    rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm V']; exact hu'
  have hWsame : ∀ W : Y.Opens, c ⁻¹ᵁ W = u ⁻¹ᵁ W ∧ ∀ i, w i ⁻¹ᵁ W = u ⁻¹ᵁ W := fun W =>
    ⟨(GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm W).symm,
      fun i => (GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm W).symm⟩
  obtain ⟨hu, _, _, _⟩ := hcomb
  refine ⟨hu', hc', hw', fun x => ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_loc
  intro p hp
  let P : Sp S := ⟨p, hp.isPrime⟩
  have hPV : u P ∈ V ⊓ V' := by
    refine ⟨(Scheme.Hom.mem_preimage u).mp ?_, (Scheme.Hom.mem_preimage u).mp ?_⟩
    · rw [hu]; trivial
    · rw [hu']; trivial
  obtain ⟨W, hWaff, hPW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hPV
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsW⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open
    (a := P) (u := ((u ⁻¹ᵁ W : (Sp S).Opens) : Set (Sp S)))
    ((Scheme.Hom.mem_preimage u).mpr hPW) (u ⁻¹ᵁ W).isOpen
  refine ⟨s, hPs, ?_⟩
  set g := algebraMap S (Localization.Away s) with hg
  have landW : ∀ f : Sp S ⟶ Y, f ⁻¹ᵁ W = u ⁻¹ᵁ W → (spMap g ≫ f) ⁻¹ᵁ W = ⊤ := by
    intro f hf
    refine lands_loc W s f fun p hp' => ?_
    rw [hf]
    exact hsW hp'
  set qs := locMap q s
  have hsq : spMap qs ≫ spMap g =
      spMap (algebraMap T (Localization ((Submonoid.powers s).map q))) ≫ spMap q := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact locMap_alg q s y
  have hws : ∀ i, spMap qs ≫ (spMap g ≫ w i) = spMap qs ≫ (spMap g ≫ u) := fun i => by
    rw [← Category.assoc, hsq, Category.assoc, hw i, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨d, hd, -, -⟩ := GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart Y W hWaff (Localization.Away s) _ qs (locMap_surj q s hq)
    (locMap_ker q s hk) ι (spMap g ≫ u) (fun i => spMap g ≫ w i) (fun i => g (a i)) (landW u rfl) hws
  have hcs := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S (Localization.Away s) g ι u c w a ⟨hu, by assumption, by assumption, by assumption⟩
  have hdc : d = spMap g ≫ c :=
    GlobalTheory.T.isAffineCombinationInChart_unique Y V hV _ ι _ _ _ _ _ (comb_mono (hWle.trans inf_le_left) _ _ _ _ hd) hcs
  have hV'd := comb_mono (hWle.trans inf_le_right) _ _ _ _ hd
  rw [hdc] at hV'd
  obtain ⟨h1, h2, h3, hx⟩ := hV'd
  have hxx := hx x
  have hsum : ∑ i, g (a i) * (chartHom V' (spMap g ≫ w i) (h3 i) x - chartHom V' (spMap g ≫ u) h1 x) =
      g (∑ i, a i * (chartHom V' (w i) (hw' i) x - chartHom V' u hu' x)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chartHom_comp V' g (w i) (hw' i) (h3 i), chartHom_comp V' g u hu' h1, map_mul, map_sub]
  rw [hsum, chartHom_comp V' g c hc' h2, chartHom_comp V' g u hu' h1] at hxx
  rw [map_sub, map_add, hxx, sub_self]

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitMod
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
end

