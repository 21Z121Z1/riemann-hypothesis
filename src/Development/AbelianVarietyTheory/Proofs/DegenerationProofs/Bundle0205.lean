import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0204
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0200

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  first | exact @GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | exact GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | (intros; apply GlobalTheory.ZH.GeoExist.hasGeo_of_hasU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem iter_lift {R K Ω : Type} [CommRing R] [Field K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    (I : Ideal R) (φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ q ∈ I) (n : ℕ) (x : R) :
    ∃ y : R, algebraMap R Ω y = (φ ^ n) (algebraMap R Ω x) ∧ y - x ^ (q ^ n) ∈ I := by
  induction n with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hI⟩ := ih
    obtain ⟨z, hz, hJ⟩ := h y
    refine ⟨z, by rw [hz, hy, pow_succ', AlgEquiv.mul_apply], ?_⟩
    rw [← Ideal.Quotient.eq] at hI hJ ⊢
    rw [hJ, map_pow, hI, ← map_pow, ← pow_mul, pow_succ]

theorem pow_pow_fixed {k : Type} [Monoid k] (c : k) (a : ℕ) (h : c ^ a = c) (n : ℕ) : c ^ (a ^ n) = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_lift_frac {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (g : A →+* L) (hg : Function.Injective g) : ∃ j : K →+* L, j.comp (algebraMap A K) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a⟩

theorem isSemiAbelian_of_rational_torsion (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l)
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left)
    (W L R K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [Algebra K L] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K'] [Algebra R K'] [IsFractionRing R K']
    [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω] [IsLocalHom (algebraMap W R)]
    (hWR : Function.Injective (algebraMap W R)) (hRΩ : Function.Injective (algebraMap R Ω))
    (hcW : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hVΩ : (algebraMap W Ω).comp (algebraMap V W) = (algebraMap K Ω).comp (algebraMap V K))
    (hk : IsAlgClosed (IsLocalRing.ResidueField R)) (hlR : IsUnit (l : R))
    (p r₀ f : ℕ) (hp : p.Prime) (hpR : CharP (IsLocalRing.ResidueField R) p) (hr₀ : 1 ≤ r₀) (hf : 1 ≤ f)
    (hres : ∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r₀) ^ m) = c)
    (σ φ : Ω ≃ₐ[K] Ω) (hfix : ∀ w : W, (φ ^ f) (algebraMap W Ω w) = algebraMap W Ω w)
    (hφ : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ (p ^ r₀) ∈ IsLocalRing.maximalIdeal R)
    (hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ (p ^ r₀))
    (hL : ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L,
      φ (σ x) = (σ ^ (p ^ r₀)) (φ x) ∧ (σ x = x → ∃ a b : R, algebraMap R Ω b ≠ 0 ∧ x * algebraMap R Ω b = algebraMap R Ω a))
    (G : Over (Sp W)) [GrpObj G] (hG : SmConn G) (hmod : IsModel (L := L) P.A G)
    (hdim : SmoothOfRelativeDimension P.g G.hom)
    (N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left)
    (hN : AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N)
    (c : ℕ) (hc : 1 ≤ c)
    (hext : ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left,
      s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left) :
    IsSemiAbelian G := by
  classical
  obtain ⟨j', hj0⟩ := exists_lift_frac (K := K') (algebraMap R Ω) hRΩ
  have hj' : ∀ x : R, j' (algebraMap R K' x) = algebraMap R Ω x := fun x => RingHom.congr_fun hj0 x
  obtain ⟨i, hi⟩ := exists_lift_frac (K := L) ((algebraMap R K').comp (algebraMap W R))
    ((IsFractionRing.injective R K').comp hWR)
  replace hi := hi.symm
  have hjW : (j'.comp i).comp (algebraMap W L) = algebraMap W Ω := by
    rw [RingHom.comp_assoc, ← hi]
    exact RingHom.ext fun w => (hj' _).trans (IsScalarTower.algebraMap_apply W R Ω w).symm
  have hjK : (j'.comp i).comp (algebraMap K L) = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) ?_
    rw [RingHom.comp_assoc, ← hcW, ← RingHom.comp_assoc, hjW, hVΩ]
  obtain ⟨θ, hθ, hθK⟩ := GlobalTheory.T.grpScheme_points_model_over_field K W L P.A G hmod Ω (j'.comp i) hjK hjW
  obtain ⟨e, act, hact, he, hpair, hrel, hdef⟩ := GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints K P Ω l (p ^ r₀) hl htors σ φ K' j' hζ
    (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
      obtain ⟨a, b, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
      refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
      rw [map_div₀, hj', hj', div_eq_iff hb0]
      exact hab.symm⟩)
  have hcard := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1
  haveI := P.isAb.comm
  have hψ : (φ ^ f).toRingEquiv.toRingHom.comp (j'.comp i) = j'.comp i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors W) ?_
    rw [RingHom.comp_assoc, hjW]
    exact RingHom.ext fun w => hfix w
  obtain ⟨t, a, m, C, Q, H, U, hm, hH, hcnt, hQ, hU, hHU, hT⟩ :=
    GlobalTheory.T.frobenius_counts_integral_torsion_specialFibre W R Ω hRΩ hk p (r₀ * f) l hp hpR (Nat.mul_pos hr₀ hf) hl hlR
      (fun c => by
        obtain ⟨m, hm, h⟩ := hres c
        refine ⟨m, hm, ?_⟩
        rw [pow_mul, ← pow_mul _ f m, mul_comm f m, pow_mul _ m f]
        exact pow_pow_fixed c _ h f)
      (φ ^ f).toRingEquiv.toRingHom (fun w => hfix w)
      (fun x => by rw [pow_mul]; exact iter_lift _ φ _ hφ f x)
      G hG P.g hdim N hN (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) θ (act (φ ^ f))
      (fun x => hθ _ hψ _ _ (hact _ x))
  rw [← map_pow, ← pow_mul] at hU hHU
  have hqq : (p ^ (r₀ * f)) ^ m = (p ^ r₀) ^ (f * m) := by rw [pow_mul, ← pow_mul _ f m]
  rw [hqq] at hU hQ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hg : P.g ≤ t + a := by
    refine GlobalTheory.T.weight_le_add_of_torsion_pairing (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) Ω l ((p ^ r₀) ^ (f * m)) P.g t a c C hl h3
      (Nat.cast_ne_zero.2 hl.ne_zero) ?_ hc hcard e he (act σ) (act (φ ^ (f * m))) (hpair _) (hrel _)
      (fun x hx => Over.OverMorphism.ext ((hact σ x).trans (htors σ x hx))) H U Q ?_ hcnt hQ hU hHU
    · rw [← pow_mul]
      exact Nat.one_lt_pow (Nat.mul_pos hr₀ (Nat.mul_pos hf hm)).ne' hp.one_lt
    · intro n x hx hS
      obtain ⟨y, hy⟩ := hdef n x hx hS
      obtain ⟨y', hy'⟩ := hθK K' i j' rfl x y hy _ hi
      obtain ⟨s, hs₁, hs₂⟩ := hext y'
      refine (hH _).2 ⟨s, hs₁, ?_⟩
      rw [← hy', ← hs₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj0]
  have hproper : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    obtain ⟨ε, -⟩ := hmod
    haveI := P.isAb.proper
    rw [← Over.w ε.hom]
    have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj P.A).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    have : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
    infer_instance
  · clear hcard
    refine GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special W L G hG hproper _ _ ?_ ?_ (hT hg)
    · ext w
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
    · intro z
      obtain ⟨m, hm, h⟩ := hres z
      have h1 : 1 < (p ^ r₀) ^ m := by
        rw [← pow_mul]
        exact Nat.one_lt_pow (Nat.mul_pos hr₀ hm).ne' hp.one_lt
      refine ⟨Polynomial.X ^ ((p ^ r₀) ^ m) - Polynomial.X, ?_, by simp [h]⟩
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast h1

theorem potentialSemistable_rational_lTorsion_any_closure (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (IsLocalRing.ResidueField V)) (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l) (hlu : IsUnit (l : V))
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) :
    PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  classical
  obtain ⟨R, _, σ, φ, hSH, hloc, hres, hW, hσ, hφ, hζ, hL⟩ := GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt V K hfin l hl hlu Ω _ rfl
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V)
  obtain ⟨p, hpV⟩ := CharP.exists (IsLocalRing.ResidueField V)
  obtain ⟨r₀, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField V) p
  rw [← Nat.card_eq_fintype_card] at hq
  rw [hq] at hres hφ hζ hL
  have hpR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap V R)).injective p
  have hVΩ : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hRΩ : Function.Injective (algebraMap R Ω) := Subtype.val_injective
  have hVR : Function.Injective (algebraMap V R) := fun a b h => hVΩ (congrArg Subtype.val h)
  obtain ⟨K', _, _, hSH⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra R K'), SH R K' := ⟨_, _, _, hSH⟩
  haveI : IsFractionRing R K' := hSH.2.2.2
  obtain ⟨jK, hjK'⟩ := exists_lift_frac (K := K) ((algebraMap R K').comp (algebraMap V R))
    ((IsFractionRing.injective R K').comp hVR)
  letI : Algebra K K' := jK.toAlgebra
  have hcomp : (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) := hjK'.symm
  obtain ⟨s, c, hc, hgeo⟩ := GlobalTheory.T.exists_neronNeutralComponent_finite_level V K R K' hSH hcomp P
  obtain ⟨W, hWd, hs, hWc, hWf, hWl, f, hf, hfix⟩ := hW s
  obtain ⟨G, _, L, _, _, _, _, hG, hcW, hmod, hdim, ⟨N, hN⟩, hext⟩ := hgeo W hWd hs hWl
  have hlR : IsUnit (l : R) := by simpa using hlu.map (algebraMap V R)
  haveI : IsLocalHom (algebraMap W R) := hWl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_rational_torsion V K l hl h3 P Ω htors W L R K' Subtype.val_injective hRΩ hcW
      (IsScalarTower.algebraMap_eq V K Ω) hSH.2.2.1 hlR p r₀ f hp hpR r₀.2 hf hres σ φ (fun w => hfix w.1 w.2) hφ hζ
      (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
        obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hab⟩⟩)
      G hG hmod hdim N hN c hc hext
  have hVW : IsLocalHom (algebraMap V W) := ⟨fun v hv => by
    have : IsUnit (algebraMap V R v) := hv.map W.val
    exact (isUnit_map_iff (algebraMap V R) v).1 this⟩
  exact ⟨W, L, inferInstance, inferInstance, hWd, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcW, hWf, hVW, hWc, G, inferInstance, hmod, hsemi⟩

theorem potModel_of_rational_torsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl h3 hlu P htors
  exact potentialSemistable_rational_lTorsion_any_closure V K hfin l hl h3 hlu P (AlgebraicClosure K) htors

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClass
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem eigen_of_expansion_in_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  intro h1 h2 hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs w₀ hw₀ α b σ Φ hσ hΦ hsupp t h
  obtain ⟨hLL, -⟩ := laws_all h1 h2
  obtain ⟨hc, -, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  have hodd : Odd S.N := by
    rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  obtain ⟨-, -, -, hval, -, hθ⟩ := hs
  obtain ⟨θ, hθs, hθa⟩ := hθ (t : S.Gam)
  obtain ⟨τ, q, hqy, hqt, hqx, hτ⟩ := GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels h1 h2 hT o Ω S ρ p y₀ u l hy x hx t
  obtain ⟨⟨w, hw⟩, -⟩ := GlobalTheory.UT.SymFrame.main hLL u.V _ hadm u.D (PadicAlgCl p) S.N hodd q
  obtain ⟨-, -, c3, c4, c5⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s b
  choose s' hs' using fun i => (c4 θ (s i)).exists
  obtain ⟨σ', hσ'⟩ := (c4 θ σ).exists
  have hσ'c : IsComb u.A s' b σ' := (c3 θ s' σ σ' hs' hσ).1 hσ'
  have hσ'c2 := c5 S.J (fun i j => y₀ (algebraMap o S.R (S.ρ t j i))) s' b σ' (fun i => hθa i _ (hs' i)) hσ'c
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hadm u.D u.A u.G u.semi u.U
  obtain ⟨hb1, hb2⟩ := hbij (PadicAlgCl p) S.N hN1 w₀ hw₀
  obtain ⟨Φ', hΦ'⟩ := (hb1 σ').exists
  have hrel := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q _ hqx θ hθs w₀ hw₀ w hw
    σ σ' Φ Φ' hΦ hΦ' hσ'
  have hwt := ((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q τ hqy
    hqt w hw).2 Φ Φ').1 hrel
  set κ : PadicAlgCl p := y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val with hκ
  have hΦeq : Φ' = (κ - 1) • Φ + Φ := by
    rw [sub_smul, one_smul, sub_add_cancel]
    refine fam_ext fun β j => ?_
    rw [hwt β j, smul_f, ← constBF_eq]
    by_cases hβ : ∀ z : u.D.toPre.X, β ≠ α + S.N • z
    · rw [hsupp β hβ j, mul_zero, mul_zero]
    · push Not at hβ
      obtain ⟨z, rfl⟩ := hβ
      rw [hτ, hκ]
      simp
  obtain ⟨⟨σ'', hσ''⟩, -⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin 2) (fun _ => σ) ![κ - 1, 1]
  have hσ''e : u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ'' ((κ - 1) • Φ + Φ) := by
    refine hlin (PadicAlgCl p) S.N w₀ σ σ σ'' Φ Φ (κ - 1) hΦ hΦ fun j => ?_
    rw [hσ'' j, Fin.sum_univ_two]
    simp [liftFun, cF]
  have heq : σ'' = σ' := (hb2 Φ').unique (hΦeq ▸ hσ''e) hΦ'
  subst heq
  obtain ⟨v1, -, v3, -⟩ := GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists h1 u.V u.A (PadicAlgCl p) S.N (x h) (e h)
  have a1 := v1 S.J s b _ σ hσ (fun i => hval i h)
  have a2 := v1 S.J s _ _ σ'' hσ'c2 (fun i => hval i h)
  have a3 := v1 (Fin 2) (fun _ => σ) _ _ σ'' hσ'' (fun _ => a1)
  rw [v3 _ _ _ a2 a3, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory.TestFibre
end

