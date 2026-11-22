import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3288
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusTorsionPointsAreLevelSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  first | (exact @GlobalTheory.LevSurjOpen.exists_open_levSurj) | (exact GlobalTheory.LevSurjOpen.exists_open_levSurj) | (intros; apply GlobalTheory.LevSurjOpen.exists_open_levSurj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPair
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Opp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem proj_quot_of_sat {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) (h : ∀ a : R, a ≠ 0 → ∀ y : M, a • y ∈ N → y ∈ N) :
    Module.Projective R (M ⧸ N) := by
  have htor : Submodule.torsion R (M ⧸ N) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact h a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat R (M ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation R (M ⧸ N) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem exists_ef_eq (D : Datum H) (ψ : D.La →+ ℤ) : ∃ y : D.La, ∀ x, D.EF y x = ψ x := by
  obtain ⟨y, hy⟩ := D.unimod.2 ψ.toIntLinearMap
  exact ⟨y, fun x => by rw [hy]; rfl⟩

theorem fin_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

variable {D : Datum H} {Z : Submodule (𝓞 E) D.La}

theorem sat_int (hZ : IsIsoSat D Z) (n : ℤ) (hn : n ≠ 0) (y : D.La) (hy : n • y ∈ Z) : y ∈ Z := by
  refine hZ.2 n.natAbs y (by omega) ?_
  rcases Int.natAbs_eq n with h1 | h1
  · rw [← natCast_zsmul, ← h1]; exact hy
  · have : ((n.natAbs : ℤ)) • y = -(n • y) := by rw [h1]; simp
    rw [← natCast_zsmul, this]; exact Z.neg_mem hy

theorem proj_int (hZ : IsIsoSat D Z) : Module.Projective ℤ (D.La ⧸ Z.restrictScalars ℤ) := by
  haveI := fin_int D
  exact proj_quot_of_sat _ fun a ha y hy => sat_int hZ a ha y hy

theorem exists_ext (hZ : IsIsoSat D Z) (φ : Z →+ ℤ) : ∃ y : D.La, ∀ z : Z, D.EF z y = φ z := by
  haveI := proj_int hZ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Z.restrictScalars ℤ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ x : D.La, x - σ ((Z.restrictScalars ℤ).mkQ x) ∈ Z := fun x => by
    have : (Z.restrictScalars ℤ).mkQ (x - σ ((Z.restrictScalars ℤ).mkQ x)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmem x⟩) fun x x' => by
    rw [← map_add]; congr 1; ext; simp only [map_add, Submodule.coe_add]; abel)
  refine ⟨-y, fun z => ?_⟩
  have h0 : (Z.restrictScalars ℤ).mkQ (z : D.La) = 0 := (Submodule.Quotient.mk_eq_zero _).2 z.2
  rw [map_neg, ef_swap, neg_neg, hy]
  simp only [AddMonoidHom.mk'_apply, h0, map_zero, sub_zero]

theorem mem_of_perp_perp (hZ : IsIsoSat D Z) (y : D.La) (hy : ∀ p ∈ perp D Z, D.EF y p = 0) : y ∈ Z := by
  haveI := proj_int hZ
  by_contra hyZ
  have hu : (Z.restrictScalars ℤ).mkQ y ≠ 0 := fun h => hyZ ((Submodule.Quotient.mk_eq_zero _).1 h)
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual ℤ (D.La ⧸ Z.restrictScalars ℤ), χ ((Z.restrictScalars ℤ).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℤ _).1 hc)
  obtain ⟨p, hp⟩ := exists_ef_eq D (χ.comp (Z.restrictScalars ℤ).mkQ).toAddMonoidHom
  have hpZ : p ∈ perp D Z := fun z hz => by
    have h0 : (Z.restrictScalars ℤ).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    rw [hp, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, h0, map_zero]
  have := hy p hpZ
  rw [ef_swap, hp, neg_eq_zero] at this
  exact hχ this

theorem perp_sat (D : Datum H) (Z : Submodule (𝓞 E) D.La) (a : 𝓞 E) (ha : a ≠ 0) (y : D.La) (hy : a • y ∈ perp D Z) :
    y ∈ perp D Z := by
  have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
  intro z hz
  have h := (perp D Z).smul_mem a' hy z hz
  rw [smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hn0

theorem exists_opp (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z) : ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  haveI := D.fin
  haveI : Module.Projective (𝓞 E) (D.La ⧸ perp D Z) := proj_quot_of_sat _ (perp_sat D Z)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (perp D Z).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hsx : ∀ q, (perp D Z).mkQ (s q) = q := fun q => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  set C := LinearMap.range s with hC
  have hdec : ∀ x : D.La, x - s ((perp D Z).mkQ x) ∈ perp D Z := fun x =>
    (Submodule.Quotient.mk_eq_zero _).1 (by rw [← Submodule.mkQ_apply, map_sub, hsx, sub_self])
  have hC0 : ∀ c ∈ C, c ∈ perp D Z → c = 0 := by
    rintro _ ⟨q, rfl⟩ h
    have : q = 0 := by rw [← hsx q]; exact (Submodule.Quotient.mk_eq_zero _).2 h
    rw [this, map_zero]
  have hsC : ∀ c ∈ C, s ((perp D Z).mkQ c) = c := by
    rintro _ ⟨q, rfl⟩; rw [hsx]
  have hZx : ∀ (z : D.La), z ∈ Z → ∀ x, D.EF z x = D.EF z (s ((perp D Z).mkQ x)) := fun z hz x => by
    have := hdec x z hz
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  have A1 : ∀ φ : Z →+ ℤ, ∃! b : C, ∀ a : Z, D.EF a b = φ a := by
    intro φ
    obtain ⟨y, hy⟩ := exists_ext hZ φ
    refine ⟨⟨s ((perp D Z).mkQ y), _, rfl⟩, fun a => (hZx a a.2 y).symm.trans (hy a), fun b hb => Subtype.ext ?_⟩
    have h1 : (b : D.La) - s ((perp D Z).mkQ y) ∈ perp D Z := fun z hz => by
      rw [ef_swap, map_sub, hb ⟨z, hz⟩, ← hZx z hz, hy ⟨z, hz⟩, sub_self, neg_zero]
    exact sub_eq_zero.1 (hC0 _ (sub_mem b.2 ⟨_, rfl⟩) h1)

  have A2 : ∀ φ : C →+ ℤ, ∃! z : Z, ∀ c : C, D.EF c z = φ c := by
    intro φ
    have hmC : ∀ x : D.La, s ((perp D Z).mkQ x) ∈ C := fun x => ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmC x⟩) fun x x' => by
      rw [← map_add]; congr 1; ext; simp only [map_add, Submodule.coe_add])
    simp only [AddMonoidHom.mk'_apply] at hy
    have hyZ : -y ∈ Z := mem_of_perp_perp hZ _ fun p hp => by
      have h0 : (perp D Z).mkQ p = 0 := (Submodule.Quotient.mk_eq_zero _).2 hp
      rw [map_neg, LinearMap.neg_apply, hy]
      have : (⟨s ((perp D Z).mkQ p), hmC p⟩ : C) = 0 := Subtype.ext (by show s ((perp D Z).mkQ p) = 0; rw [h0, map_zero])
      rw [this, map_zero, neg_zero]
    have key : ∀ c : C, D.EF c (-y) = φ c := fun c => by
      rw [ef_swap, map_neg, LinearMap.neg_apply, neg_neg, hy]
      congr 1; exact Subtype.ext (hsC c c.2)
    refine ⟨⟨-y, hyZ⟩, key, fun z hz => Subtype.ext ?_⟩
    have hw : ∀ x, D.EF ((z : D.La) - -y) x = 0 := fun x => by
      have h1 := hz ⟨_, hmC x⟩
      have h2 := key ⟨_, hmC x⟩
      rw [hZx _ (sub_mem z.2 hyZ), ef_swap, map_sub]
      rw [h1, h2, sub_self, neg_zero]
    exact sub_eq_zero.1 (D.unimod.1 (LinearMap.ext fun x => by rw [hw, map_zero, LinearMap.zero_apply]))
  let β : LinearMap.BilinForm ℤ C := LinearMap.mk₂ ℤ (fun a b : C => -D.EF a b)
    (fun a a' b => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; abel) (fun n a b => by simp) (fun a b b' => by simp only [Submodule.coe_add, map_add]; abel) (fun n a b => by simp)
  obtain ⟨t, ht⟩ := exists_skew_solve A2 β (fun a b => by
      show -D.EF a b = -(-D.EF b a)
      rw [ef_swap D a b]) (fun c a b => by
      show -D.EF ((c • a : C) : D.La) b = -D.EF a ((H.bar c • b : C) : D.La)
      rw [Submodule.coe_smul, Submodule.coe_smul, D.adj])
  have ht' : ∀ a b : C, D.EF a (t b) + D.EF (t a) b = -D.EF a b := ht
  let g : C →ₗ[𝓞 E] D.La := C.subtype + Z.subtype ∘ₗ t
  have hg : ∀ c, g c = c + t c := fun c => rfl
  have kZ : ∀ (a : Z) (c : C), D.EF a (g c) = D.EF a c := fun a c => by
    rw [hg, map_add, hZ.1 a.2 _ (t c).2, add_zero]
  refine ⟨LinearMap.range g, hZ.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    show D.EF (g b) (g b') = 0
    have h0 : D.EF (t b) (t b') = 0 := hZ.1 (t b).2 _ (t b').2
    rw [hg, hg]
    simp only [map_add, LinearMap.add_apply]
    linear_combination ht' b b' + h0
  · obtain ⟨b, hb, hu⟩ := A1 φ
    refine ⟨⟨g b, b, rfl⟩, fun a => (kZ a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg g (hu b' fun a => (kZ a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := A2 (-(φ.comp g.rangeRestrict.toAddMonoidHom))
    refine ⟨a, ?_, fun a' ha' => hu a' fun c => ?_⟩
    · rintro ⟨_, c, rfl⟩
      show D.EF a (g c) = φ ⟨g c, c, rfl⟩
      rw [kZ, ef_swap, ha c, AddMonoidHom.neg_apply, neg_neg]
      rfl
    · have h1 := ha' ⟨g c, c, rfl⟩
      rw [ef_swap, ← kZ a' c]
      show -D.EF a' (g c) = -φ ⟨g c, c, rfl⟩
      rw [← h1]

end GlobalTheory.LowFilt.Opp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogo
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨θ, hθ⟩ := exists_theta_vec D m
  obtain ⟨ζ, hζZ, -, hζs, hopp⟩ := h.exists_rank_one hm θ hθ
  have himg' : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg'' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ (Z'.subtype + ℓ.smulRight (m + ζ ℓ)) = y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ)) := by
      ext x; simp
    rw [img, ← LinearMap.range_comp, this]
  have he𝔭 : e ∉ 𝔭 := fun h' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' he1))
  have hℓv : (e • ℓ₀) v ∉ 𝔭 := by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact fun h' => (h𝔭.isPrime.mem_or_mem h').elim he𝔭 hℓ₀
  have hker := range_le_of_ker (y ∘ₗ Z'.subtype) (e • ℓ₀) (y (m + ζ (e • ℓ₀))) 𝔭 h𝔭 (v := v) hv hℓv
  refine ⟨_, hopp (e • ℓ₀), fun 𝔮 h𝔮 hn𝔮 => ?_, ?_⟩
  · rw [himg', himg'']
    by_cases hq : 𝔮 = 𝔭
    · subst hq; exact hker.2
    · exact range_le_of_mem _ _ _ 𝔮 fun x => by
        rw [LinearMap.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · rw [himg'']
    intro hle
    have hu' := hle hker.1
    have hz : y (ζ (e • ℓ₀)) ∈ img D y Z' 𝔭 := by
      rcases hA with hA | hA
      · haveI := h𝔭
        have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
        have hn' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
        have he' := he _ h𝔭' hn' hA
        rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at he'
        have hbe : H.bar e ∈ 𝔭 := by
          have : H.bar.symm e = H.bar e := by rw [RingEquiv.symm_apply_eq, bar_bar]
          rwa [this] at he'
        rw [hζs, map_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem_smul hbe trivial)
      · exact hA (Submodule.mem_map_of_mem (hζZ _))
    apply hym
    have : y m = y (m + ζ (e • ℓ₀)) - y (ζ (e • ℓ₀)) := by simp
    rw [this]
    exact sub_mem hu' hz

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.PQuot

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem sections_triv {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ^ c = 1) :
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  have hP := o.isLB
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb hP _ _
  have clsPow : GlobalTheory.CechPic.cls (Hecke.lbPow o.P c) hQ = c • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin c) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = c • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow, map_nsmul]
  have hQth : GlobalTheory.AbDual.evc hQ (toUnit o.A ≫ h) (𝟙 o.A) = 0 := by
    rw [evcQ, ← evc_pow_left o.ab hP o.rig₁ o.rig₂, ← MonObj.comp_pow, hh, MonObj.comp_one]
    exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

theorem exists_quot {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e) (hp : IsUnit ((p : ℕ) : R))
    (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (hfin : Finite H)
    (hfree : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ H →
      toUnit (Over.mk x) ≫ h = 1 → h = 1)
    (stab : ∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hiso : ∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1)
    (hmax : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 →
      (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) :
    ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧
      ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A),
        g ≫ ψ = 1 ↔ ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    H o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  choose actf hactf using fun c' : D.O => GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme S o.A A' H ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ c H
    (fun h hh => (sections_triv o c h (hpow h hh)).1) (fun h hh => (sections_triv o c h (hpow h hh)).2) hiso
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' H ψ hψ hgal
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (sq2 ψ) _ _
    (Hecke.lbPow o.P c) hGC (DVR.linComb_isLB _ o.isLB _ _) u hu hcoc
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b N S s o A' ψ hψ _ P₀ hP₀ w₀
  have hc1 : 1 ≤ c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient p D R b N S s o A' act' ψ _ _ hA' hψ hgal hcomp
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b N S s o A' ψ _ hA' hψ hgal _ P' hP' w r1 r2
      ample := GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b N S s o A' ψ _ hA' hψ hgal _ hc1 P' hP' w
      kerP := GlobalTheory.T.descendedBundle_kernel_killed_primeToP p D R b N S s o c hc hp H A' ψ hA' hψ hgal hmax P' hP' r1 r2 w
      rosati := GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b N S s o A' act' ψ _ hA' hψ hgal hcomp _ P' hP' w r1 r2
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta x ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (c' • x) ≫ ψ = (o.eta x ≫ ψ) ≫ act'.act c'
        rw [o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, one_comp]
      geom := GlobalTheory.T.exists_tateSimilitude_quotient_by_pGroup_sections p D R b N S s o c hc H A' ψ hA' hψ hgal hpow act' hcomp P' hP' r1 r2 w }
  have hmk : IsMonHom (𝟙 o.A ^ c) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_mulA c
  obtain ⟨ψ', hψ'h, hψ'⟩ := GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme S o.A A' o.A H ψ hψ hgal (𝟙 o.A ^ c) hmk
    (fun h hh => by rw [MonObj.comp_pow, Category.comp_id, hpow h hh])
  refine ⟨o', ψ, ⟨hc, hψ, hcomp, fun x => rfl, ⟨w⟩, ψ', hψ'h, hψ', ?_⟩, fun κ _ _ x t => ⟨fun ht => ?_, ?_⟩⟩
  · show ψ' ≫ ψ = 𝟙 A' ^ c
    rw [← cancel_epi ψ, ← Category.assoc, hψ', MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have ht' : t ≫ ψ = (1 : Over.mk x ⟶ A') := ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht', MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hgal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    refine ⟨h.1, h.2, ?_⟩
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt]
  · rintro ⟨h, hh, rfl⟩
    show (toUnit (Over.mk x) ≫ h) ≫ ψ = (1 : Over.mk x ⟶ A')
    rw [Category.assoc, kill h hh, MonObj.comp_one]

theorem exists_pairing {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e)
    (κ : Type) [Field κ] [IsAlgClosed κ] (hp : ((p : ℕ) : κ) ≠ 0) (x : Sp κ ⟶ S) :
    ∃ e : (Over.mk x ⟶ o.A) → (Over.mk x ⟶ o.A) → κˣ,
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : Over.mk x ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : Over.mk x ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : Over.mk x ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ c = 1 → (∀ g' : Over.mk x ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) := by
  have hcκ : (c : κ) ≠ 0 := by
    obtain ⟨e, rfl⟩ := hc
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp
  obtain ⟨e, he, hl, hr⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes S o.A o.P o.ab o.isLB κ x c hcκ
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hinj : Function.Injective (unitOn (R := κ)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of κ)).symm.commRingCatIsoToRingEquiv.injective
  have hmul : ∀ u v : κˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v => map_mul (Units.map _) u v
  have hone : unitOn (1 : κˣ) = 1 := map_one (Units.map _)
  have hval : ∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      Out.WeilIs (G2 o.A) o.P c (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') (unitOn (e g g')) :=
    fun g g' hg hg' => GlobalTheory.BiextPairing.weilIs_of_hecke_lbPow hG2 o.isLB c ((he g g' hg hg' _).2 rfl)
  have hact : ∀ (a : D.O) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (g ≫ o.act.act a) ^ c = 1 := fun a g hg => by
    haveI := o.act.hom a
    rw [← MonObj.pow_comp, hg, MonObj.one_comp]
  refine ⟨e, he, hl, hr, fun a g g' hg hg' => hinj ?_, fun g g' hg hg' => hinj ?_, fun g hg h => ?_⟩
  · exact GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso S o.A o.P o.ab o.isLB _ _ (o.act.hom a) (o.act.hom _) (o.rosati a) c _ g g' _ _
      (hval _ _ (hact a g hg) hg') (hval _ _ hg (hact _ g' hg'))
  · have h1 := GlobalTheory.CommPairing.weilIs_symm o.isLB (hval g' g hg' hg)
    have h2 := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm c _ g g' _ _ h1 (hval g g' hg hg')
    rw [hmul, hone, ← h2]
    exact inv_mul_cancel _
  · obtain ⟨e₀, he₀, hker⟩ := o.kerP
    have h1 := hker _ g (GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ κ x c hcκ g hg (fun g' hg' => by
      have := hval g g' hg hg'
      rwa [h g' hg', hone] at this))
    have hco : e₀.Coprime c := by
      obtain ⟨e, rfl⟩ := hc
      exact he₀.pow_right e
    exact (pow_eq_one_iff_of_coprime hco).1 ⟨h1, hg⟩

theorem max_geom {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : (c : k) ≠ 0)
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A)) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hmax : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H)
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ o.A) (hg : g ^ c = 1)
    (ho : ∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) : ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨g₀, hg₀, rfl⟩ := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hc).2 κ x g hg
  refine ⟨g₀, hmax g₀ hg₀ fun h hh => ?_, rfl⟩
  obtain ⟨e, he, -, -⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes (Sp k) o.A o.P o.ab o.isLB k (𝟙 _) c hc
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨u, hu⟩ : ∃ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g₀ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) u := ⟨_, (he g₀ h hg₀ (hpow h hh) _).2 rfl⟩
  have h1 := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hG2 hQ (toUnit (Over.mk x)) hu
  rw [comp_lift, comp_lift, MonObj.comp_one] at h1
  have h2 := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hG2 hQ h1 (ho h hh)
  have hinj : Function.Injective (toUnit (Over.mk x)).left.appTop.hom := by
    have e1 : (toUnit (Over.mk x)).left = x := by simp
    rw [e1]
    haveI : Nontrivial Γ(Sp κ, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    letI : Field Γ(Sp k, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)).toField
    exact RingHom.injective x.appTop.hom
  have hu1 : u = 1 := Units.map_injective (f := (toUnit (Over.mk x)).left.appTop.hom.toMonoidHom) hinj
    (h2.trans (map_one _).symm)
  rwa [hu1] at hu

end GlobalTheory.UPel.HT.ES.PQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmul
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem exists_isLie_add_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE l
  exact lie_surj_mod_p p O E hE G d c l

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix : ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  first | (exact @GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (exact GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (intros; apply GlobalTheory.ZarhinFam.exists_spanning_family_posDef  <;> assumption)
end

