import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Frames

open GlobalTheory.CompanionTheory.Ar

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {i : Ω₀ →+* Ω} {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li]
  [AddCommGroup Li₀] [Module Ω₀ Li₀] {ι : Li₀ →+ Li}

theorem linearIndependent_comp_basis (h : IsExtOver i ι) {K : Type} (B : Module.Basis K Ω₀ Li₀) :
    LinearIndependent Ω fun k => ι (B k) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e : s ≃ Fin s.card := s.equivFin
  have hb : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k : K)) :=
    B.linearIndependent.comp (fun k => (e.symm k : K)) (Subtype.val_injective.comp e.symm.injective)
  have h3 := (h.2 s.card _ hb).comp e e.injective
  convert h3 using 1
  funext x
  simp

theorem exists_dual_ext (h : IsExtOver i ι) (hs : Submodule.span Ω (Set.range ι) = ⊤)
    (φ : Module.Dual Ω₀ Li₀) : ∃ φ' : Module.Dual Ω Li, ∀ e, φ' (ι e) = i (φ e) := by
  classical
  let B := Module.Basis.ofVectorSpace Ω₀ Li₀
  have hli : LinearIndependent Ω fun k => ι (B k) := linearIndependent_comp_basis h B
  have hmem : ∀ e : Li₀, ι e ∈ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    intro e
    have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [h.1]; exact Submodule.smul_mem _ _ hx
  have hsp : ⊤ ≤ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact hmem e
  let B' := Module.Basis.mk hli hsp
  refine ⟨B'.constr Ω (fun k => i (φ (B k))), fun e => ?_⟩
  have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hk : ι (B k) = B' k := (Module.Basis.mk_apply hli hsp k).symm
    rw [hk, Module.Basis.constr_basis]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [h.1]
    simp only [map_smul, hx, smul_eq_mul, map_mul]

theorem two_frames (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li) (hext : IsExtOver i ι)
    (hs : Submodule.span Ω (Set.range ι) = ⊤) (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ)
    (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω)
    (m : Ω₀) (hL : Submodule.span W L = Submodule.span W (ι '' L₀))
    (hT : ∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) (hTb : ∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j))
    (hm : ∀ j, m • b₀ j ∈ L₀) (hπ : ∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0)
    (hint : ∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) (hκ : ∀ j, κ • b j ∈ L)
    (hb : ∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) :
    (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧
      ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  classical
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hin : ι (m • b₀ j) ∈ Submodule.span W L := by
      rw [hL]; exact Submodule.subset_span ⟨_, hm j, rfl⟩
    have key : ∀ x ∈ Submodule.span W L, T x ∈ Submodule.span W (Set.range b) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hT y hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy =>
        rw [Subring.smul_def, map_smul]
        have hw := Submodule.smul_mem _ w hy
        rwa [Subring.smul_def] at hw
    have hj := key _ hin
    rwa [hext.1, map_smul, hTb, smul_smul, mul_comm] at hj
  · have hv : κ • b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a)) :=
      Submodule.smul_mem _ κ (hb j)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hv
    have hcW : ∀ a, i m * c a ∈ W := by
      intro a
      obtain ⟨ψ, hψ⟩ := exists_dual_ext hext hs (π₀ a)
      have hψv : ψ (κ • b j) = c a := by
        rw [← hc, map_sum, Finset.sum_eq_single a]
        · rw [map_smul, hψ, hπ, if_pos rfl, map_one, smul_eq_mul, mul_one]
        · intro x _ hx
          rw [map_smul, hψ, hπ, if_neg (Ne.symm hx), map_zero, smul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hspan : κ • b j ∈ Submodule.span W (ι '' L₀) := by
        rw [← hL]; exact Submodule.subset_span (hκ j)
      have key : ∀ x ∈ Submodule.span W (ι '' L₀), i m * ψ x ∈ W := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨e, he, rfl⟩ := hy
          rw [hψ, ← map_mul]; exact hint a e he
        | zero => simp
        | add y z _ _ hy hz => rw [map_add, mul_add]; exact W.add_mem hy hz
        | smul w y _ hy =>
          rw [Subring.smul_def, map_smul, smul_eq_mul, mul_left_comm]
          exact W.mul_mem w.2 hy
      rw [← hψv]; exact key _ hspan
    rw [mul_smul, ← hc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [smul_smul]
    have ha := Submodule.smul_mem (Submodule.span W (Set.range fun a => ι (b₀ a))) (⟨_, hcW a⟩ : W)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at ha

end GlobalTheory.CompanionTheory.Ar.Frames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieTangent

theorem existsUnique_semilinear_lifts :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R')
      (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E']
      (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'),
      ∃! j : E →ₛₗ[c] E', ∀ e, M.Lifts c (𝟙 G.left) e (M'.pt (j e)) := by
  intro S G _ R R' _ _ c x E _ _ E' _ _ M M'
  have hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x := rfl
  have h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base c hc (M.tan e))
  choose a ha using h
  refine ⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro e e'
    apply M'.inj
    rw [M'.add, ha, ha, ha, M.add, MonObj.comp_mul]
  · intro r e
    apply M'.inj
    rw [M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]
  · intro e
    change (M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left
    rw [Category.comp_id, ha]
    rfl
  · intro j hj
    ext e
    refine M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)
    apply Over.OverMorphism.ext
    have := hj e
    unfold LieModel.Lifts at this
    rw [Category.comp_id] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringChartPoint
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

abbrev chartRing {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem stalk_value (hg : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (p : Cpt ξ) (φ : regAt ξ p →+* R)
    (z : Spec (CommRingCat.of R) ⟶ X) (hzc : centre z = p.1) (hv : ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a))
    (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)) :
    ∃ hm : genMap ξ ⟨centre z, h⟩ s ∈ regAt ξ p,
      (Scheme.stalkClosedPointTo z).hom s = φ ⟨genMap ξ ⟨centre z, h⟩ s, hm⟩ := by
  obtain ⟨pp, hpp⟩ := p
  dsimp only at hzc
  subst hzc
  refine ⟨⟨s, rfl⟩, ?_⟩
  obtain ⟨h', s', e1, e2⟩ := hv ⟨genMap ξ ⟨centre z, h⟩ s, ⟨s, rfl⟩⟩
  have e3 : s' = s := hg.inj ⟨centre z, h⟩ e1
  subst e3
  exact e2

set_option backward.isDefEq.respectTransparency false in

theorem spec_square {F : Type} [Field F] (θ : Ω →+* F) {A : Subring F} [IsLocalRing A]
    (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) :
    Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  have e : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) := RingHom.ext hs
  have e1 := LieTangent.spec_centre z
  have e2 := LieTangent.spec_genMap ξ ⟨centre z, h⟩
  calc Spec.map (CommRingCat.ofHom A.subtype) ≫ z
      = Spec.map (CommRingCat.ofHom A.subtype) ≫
          (Spec.map (CommRingCat.ofHom (R := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom) ≫
            X.fromSpecStalk (centre z)) := by rw [e1]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ (Spec.map (CommRingCat.ofHom (genMap ξ ⟨centre z, h⟩)) ≫
            X.fromSpecStalk (centre z)) := by
        rw [← Category.assoc, ← Category.assoc, LieTangent.spec_comp, LieTangent.spec_comp, e]
    _ = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
        exact congrArg (_ ≫ ·) e2

theorem point_of_local_subring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  intro X Ω _ ξ κ x c hT hc F _ θ A _ hA
  have hC : ∀ s ∈ chartRing x c, θ s ∈ A := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hA j
    | algebraMap r =>
      have : θ (algebraMap ℤ Ω r) = (r : F) := by simp
      rw [this]
      exact intCast_mem A r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let θC : chartRing x c →+* A :=
    (θ.comp (chartRing x c).val.toRingHom).codRestrict A (fun s => hC s s.2)
  obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc
    (Ideal.comap θC (IsLocalRing.maximalIdeal A)) inferInstance
  have hunit : ∀ s (hs : s ∈ chartRing x c), unitAt ξ p s ↔ IsUnit (⟨θ s, hC s hs⟩ : A) := by
    intro s hs
    rw [← hpu ⟨s, hs⟩, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    rfl
  have hreg : ∀ a ∈ regAt ξ p, θ a ∈ A := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 ha
    obtain ⟨u, hu⟩ := (hunit s hs).1 hsu
    have h1 : (((u⁻¹ : Aˣ) : A) : F) * θ s = 1 := by
      have h2 := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at h2
      exact h2
    have h3 : θ a = (((u⁻¹ : Aˣ) : A) : F) * θ (s * a) := by
      rw [map_mul, ← mul_assoc, h1, one_mul]
    rw [h3]
    exact mul_mem ((u⁻¹ : Aˣ) : A).2 (hC _ hsa)
  let φ : regAt ξ p →+* A := (θ.comp (regAt ξ p).subtype).codRestrict A (fun a => hreg a a.2)
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨s, hs, hsu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hpc a).1 a.2
    have hua : IsUnit (⟨θ (s * a), hC _ hsa⟩ : A) := by
      have h1 : (⟨θ (s * a), hC _ hsa⟩ : A) = ⟨θ s, hC s hs⟩ * φ a :=
        Subtype.ext (map_mul θ s a)
      rw [h1]
      exact ((hunit s hs).1 hsu).mul ha
    obtain ⟨h0, -, hi⟩ := (hunit _ hsa).2 hua
    have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
    have ha0 : (a : Ω) ≠ 0 := right_ne_zero_of_mul h0
    have hinv : (a : Ω)⁻¹ ∈ regAt ξ p := by
      have h1 : (a : Ω)⁻¹ = s * (s * a)⁻¹ := by field_simp
      rw [h1]
      exact mul_mem hsu.2.1 hi
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  obtain ⟨z, ⟨hzc, hzv⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hT.gen p A φ hloc
  have h : genPt ξ ⤳ centre z := by rw [hzc]; exact p.2
  have hp : (⟨centre z, h⟩ : Cpt ξ) = p := Subtype.ext hzc
  have hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s) := by
    intro s
    obtain ⟨hm, e⟩ := stalk_value hT.gen p φ z hzc hzv h s
    rw [e]
    rfl
  exact ⟨z, h, by rw [hp]; exact hpc, hs, spec_square θ z h hs⟩

end GlobalTheory.CompanionTheory.Ar.ChartPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemRegAtOfCodimOne
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_point_of_prime {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (p : Cpt ξ) (P : Ideal (regAt ξ p)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ringKrullDim (X.presheaf.stalk q.1) = (P.height : WithBot ℕ∞) ∧
      ∀ a ∈ regAt ξ q, ∃ s t : regAt ξ p, s ∉ P ∧ a * s = t := by
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  let e := RegAtRing.stalkEquiv h p
  let P' : Ideal (X.presheaf.stalk p.1) := P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)
  have localization₂ := hU.isLocalization_stalk ⟨p.1, hp⟩
  let 𝔮 : Ideal Γ(X, U) := P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨𝔮, h𝔮⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this

  have hsp : hU.fromSpec y ⤳ p.1 := by
    have hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩ := by
      change 𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal
      rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk p.1)
        (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this

  have hgy : genPt ξ ⤳ hU.fromSpec y := by
    have hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y := by
      change (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮
      intro r hr
      letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)
      have locG := hU.isLocalization_stalk ⟨genPt ξ, hg⟩
      have hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r) := by
        rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk (genPt ξ))
          (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal] at hr
        exact (IsLocalRing.mem_maximalIdeal _).1 hr
      have hz : (Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r) = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r))⁻¹
        apply hnu
        refine IsUnit.of_mul_eq_one w (h.bij.1 ?_)
        erw [map_mul, hw, map_one]
        exact mul_inv_cancel₀ hne
      have hz' : X.presheaf.germ U p.1 hp r = 0 := by
        apply h.inj p
        rw [RegAtRing.genMap_germ p U hp hg, hz, map_zero]
      change algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'
      erw [hz']
      exact P'.zero_mem
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this
  letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)
  have locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  have locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮 := locY
  refine ⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩
  · have h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))
    have h2 : 𝔮.height = P'.height :=
      IsLocalization.height_comap (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'
    have h3 : P'.height = P.height := RingEquiv.height_comap e P
    change ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _
    rw [h1, h2, h3]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj y.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec y)) x
    have he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 =
        (X.presheaf.germ U (hU.fromSpec y) hyU).hom r := he
    have hgt := RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU
    refine ⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩
    · exact t.2
    · change genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) =
        genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)
      rw [← hgt, ← hgt, ← map_mul]
      exact congrArg _ he'

theorem mem_regAt_of_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (p : Cpt ξ) (a : Ω),
    (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → a ∈ regAt ξ q) →
    a ∈ regAt ξ p := by
  intro X Ω _ ξ _ h hn p a ha
  obtain ⟨hfr, hno, -⟩ := RegAtRing.regAt_ring X Ω ξ h p
  have : IsFractionRing (regAt ξ p) Ω := hfr
  have : IsNoetherianRing (regAt ξ p) := hno inferInstance
  have : IsIntegrallyClosed (regAt ξ p) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn p x hx⟩, rfl⟩
  obtain ⟨t, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (regAt ξ p) Ω d ≠ 0 := by
    simpa using hd0
  obtain ⟨b, hb⟩ := mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d
    (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0
    ⟨1, t, by field_simp⟩
    (fun P hP h1 _ => by
      obtain ⟨q, hq, hdim, hiff⟩ := exists_point_of_prime h p P hP
      have hmem := ha q hq (by rw [hdim]; simp [h1])
      obtain ⟨s, u, hs, hsu⟩ := hiff _ hmem
      exact ⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)
  rw [← hb]
  exact b.2

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertible
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

theorem mul_inv_apply_eq_det_div {K : Type} [Field K] {n r m : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (J : Fin m → Fin n) (c : Fin m → Fin r) (j : Fin n) (l : Fin m) :
    ((F.submatrix id c) * (F.submatrix J c)⁻¹) j l =
      (F.submatrix (Function.update J l j) c).det / (F.submatrix J c).det := by
  have hrow : F.submatrix (Function.update J l j) c =
      (F.submatrix J c).updateRow l (fun k => F j (c k)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply, Function.update_apply]
    split_ifs <;> rfl
  have key : (F.submatrix (Function.update J l j) c).det =
      ∑ k, F j (c k) * (F.submatrix J c).adjugate k l := by
    rw [hrow, ← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, Matrix.mul_apply, Matrix.inv_def, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  ring

theorem split_of_regular_ratios (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K)
    (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r)
    (J : Fin ((k : ℕ) + 1) → Fin n) (hA : ∀ j l, A j l ∈ R) (hB : ∀ l j, B l j ∈ R) (hBA : B * A = 1)
    (_ha : a ≠ 0) (hdet : ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0)
    (hR : ∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det /
      ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) :
    ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧
      ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  have hN' : (a • (A * G)).submatrix id (Fin.castLE k.2) = A * (a • G.submatrix id (Fin.castLE k.2)) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.mul_apply, id_eq, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r) (Fin ((k : ℕ) + 1)) K,
      Q = (a • G.submatrix id (Fin.castLE k.2)) * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ :=
    ⟨_, rfl⟩
  have hAQ : A * Q = (a • (A * G)).submatrix id (Fin.castLE k.2) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ := by
    rw [hQ, ← Matrix.mul_assoc, ← hN']
  have hBQ : Q = B * (A * Q) := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hPR : ∀ j l, (A * Q) j l ∈ R := by
    intro j l
    rw [hAQ, mul_inv_apply_eq_det_div]
    exact hR l j
  refine ⟨fun l i => Q i l, fun l i => A (J l) i, ?_, ?_, ?_, ?_⟩
  · intro l i
    show Q i l ∈ R
    rw [hBQ, Matrix.mul_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hB i j) (hPR j l)
  · intro l i
    exact hA (J l) i
  · intro l l'
    change (A * Q) (J l) l' = _
    rw [hAQ]
    change (((a • (A * G)).submatrix J (Fin.castLE k.2)) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹) l l' = _
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]
  · intro l
    have hD : (fun i => Q i l) = ∑ c : Fin ((k : ℕ) + 1),
        (a * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ c l) • (fun i => G i (Fin.castLE k.2 c)) := by
      funext i
      rw [hQ]
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul,
        Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun c _ => by ring
    show (fun i => Q i l) ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1)
    rw [hD]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_image_of_mem (fun c i => G i c)
        (show (Fin.castLE k.2 c : Fin r) ∈ {c' : Fin r | (c' : ℕ) < (k : ℕ) + 1} from c.2)))

end GlobalTheory.CompanionTheory.Ar.FlagBun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_fraction_noetherian_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | exact GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring <;> assumption)
end

