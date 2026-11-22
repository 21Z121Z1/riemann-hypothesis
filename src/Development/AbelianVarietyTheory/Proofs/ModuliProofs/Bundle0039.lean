import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapExtendingOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.arith_and_proOpen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β)
    (hβ : IsDedFrac β) (hO : Algebra.FiniteType ℤ O) :
    (∃ z : C.X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j := by
  obtain ⟨⟨hdom, hded⟩, hchar, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have h := GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨⟨C.s ≫ spMap (algebraMap ℤ O), ?_, ?_⟩, h.2.2.2⟩
  · have hprop : IsProper C.s := by
      obtain ⟨N, i, hi, e⟩ := C.proj
      have := isProper_str O N
      rw [← e]; infer_instance
    have : LocallyOfFiniteType (spMap (algebraMap ℤ O)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr hO
    infer_instance
  · have := C.flat
    have : Flat (spMap (algebraMap ℤ O)) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    infer_instance

theorem exists_sabMap_extending_of_iso : ((∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  intro hS hT E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C C' r ν f hβ hO hp hj
  obtain ⟨hz, h1, h2, h3, h4⟩ := C'.arith_and_proOpen hβ hO
  obtain ⟨PP', cub, sym, adj, prim, p, -⟩ := sabPull Out.CubePf.cubePull f C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_base_eq n (g := C'.j ≫ f) hj.symm
  obtain ⟨a', ha'⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ p n'
  obtain ⟨b, hb⟩ := hS hT E H C'.X U' C'.j ⟨C'.normal, hz⟩ h1 h2 h3 h4 t' C'.t _ C'.m a' hp
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ p b
  obtain ⟨mu, hmu⟩ := GlobalTheory.exists_sabMap_of_base_eq m (Category.id_comp f)
  refine ⟨mu, ?_⟩
  exact (congrArg (C'.m.φ ≫ ·) (hmu.trans hm)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ p.φ) hb).trans (ha'.symm.trans (hn'.trans hn))))

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulMemSpanInvariantsSup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_mem_span_invariants_sup :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B] (N : Type)
      [AddCommGroup N] [Module B N] [DistribMulAction Γ N],
      (∀ (g : Γ) (b : B) (x : N), g • (b • x) = (g • b) • (g • x)) → ∀ q : Ideal B, q.IsPrime →
      (Nat.card (q.inertia Γ) : B) ∉ q →
      (∀ g ∈ q.inertia Γ, ∀ x : N, g • x - x ∈ q • (⊤ : Submodule B N)) →
      ∀ x : N, ∃ s : B, s ∉ q ∧
        s • x ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} ⊔ q • (⊤ : Submodule B N) := by
  intro Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, c, d, s, hs, hsep⟩ := exists_sum_smul_separating_inertia Γ B q hq

  refine ⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩

  have hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y} := by
    intro j h
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x) := ⟨_, rfl⟩
  have hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} := by
    rw [hzdef]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))
  have hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x) := by
    rw [hzdef]
    simp only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x
      = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]

  have hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N) := by
    rw [hz', hsumI, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hg : g ∈ q.inertia Γ
    · rw [if_pos hg]
      have e : (∑ j, d j * g • c j) • (g • x) - s • x
          = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top)
        (Submodule.smul_mem _ s (htriv g hg x))
    · rw [if_neg hg, sub_zero]
      exact Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top
  have key := Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)
  rwa [sub_sub_cancel] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.ListedSubgroup

variable {S : Scheme.{0}}

theorem eq_comp_section {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by
  have := isClosedImmersion_of_section_of_isSeparated f s hs
  have hsurj : Surjective (pullback.fst z s) := by
    refine ⟨fun y => ?_⟩
    obtain rfl : y = q := Subsingleton.elim _ _
    have h : y ∈ Set.range (pullback.fst z s) := by
      rw [Scheme.Pullback.range_fst]
      exact hz
    exact h
  have : IsIso (pullback.fst z s) := isIso_of_isClosedImmersion_of_surjective _
  rw [← cancel_epi (pullback.fst z s)]
  simp only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]

theorem section_eq [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  obtain ⟨a', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N a ha
  obtain ⟨b', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N b hb
  have hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N := by
    rw [Category.assoc, Category.assoc]
    exact Over.OverMorphism.ext h
  have hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1 := by
    rw [Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]
  have hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b' :=
    (LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm
  have : a' = b' := Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x
      (congrArg CommaMorphism.left hab))
  rw [this]

end GlobalTheory.HkFam.ListedSubgroup

namespace GlobalTheory.HkFam

open ListedSubgroup in

theorem exists_subgroup_eq_range_of_lists :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) [ConnectedSpace S] (t : SAB H S) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (K : Set t.G.left), IsProper t.G.hom → IsUnit (p : Γ(S, ⊤)) → Lists (p ^ 2) σ K → HeckeSet D t 𝔓 p i K → ∃ C : Subgroup (𝟙_ (Over S) ⟶ t.G), (C : Set _) = Set.range σ := by
  intro E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  have hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hp.pow 2
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, -⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j => by
    rw [hC, hK]
    rintro _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩
  have key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ := by
    intro a ha h
    rw [hC, hK] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨q, rfl⟩)
    have h1 := eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w (toUnit (Over.mk x) ≫ a)] at h1
    exact ⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩
  refine ⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩
    refine key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_
    rw [MonObj.comp_mul]
    exact C.mul_mem (hmem j) (hmem j')
  · refine key _ (one_pow _) ?_
    rw [MonObj.comp_one]
    exact C.one_mem
  · rintro _ ⟨j, rfl⟩
    refine key _ (by rw [inv_pow, hσ, inv_one]) ?_
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hmem j)

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isIntegral_of_densePart {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U

theorem existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component T
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DenseBasis

variable {Z S : Scheme.{0}}

theorem isOpenImmersion_section (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) :
    IsOpenImmersion σ := by
  have : Etale (σ ≫ p) := by rw [hσ]; infer_instance
  have : Etale σ := Etale.of_comp σ p
  have : IsSplitMono σ := IsSplitMono.mk' ⟨p, hσ⟩
  exact IsOpenImmersion.of_flat_of_mono σ

theorem comp_section_eq_iff (p : Z ⟶ S) [Etale p] (σ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S)
    {K : Type} [Field K] (y : Spec (.of K) ⟶ Z) (w : Spec (.of K)) :
    (y ≫ p) ≫ σ = y ↔ y w ∈ Set.range σ := by
  have := isOpenImmersion_section p σ hσ
  constructor
  · intro h
    refine ⟨(y ≫ p) w, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec (.of K) ⟶ Z => f w) h
  · intro h
    have hr : Set.range y ⊆ Set.range σ := by
      rintro _ ⟨v, rfl⟩
      rwa [Subsingleton.elim v w]
    rw [← IsOpenImmersion.lift_fac σ y hr]
    simp only [Category.assoc, reassoc_of% hσ]

theorem exists_lift (p : Z ⟶ S) [IsFinite p] [Etale p] {K : Type} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ S) (w : Spec (.of K)) (z : Z) (hz : p z = x w) :
    ∃ y : Spec (.of K) ⟶ Z, y ≫ p = x ∧ y w = z := by
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z w hz
  obtain ⟨n, e, he⟩ := GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed (pullback.snd p x)
  obtain ⟨⟨j, v⟩, hv⟩ : ∃ a, AlgebraicGeometry.sigmaMk _ a = e.inv q :=
    ⟨(AlgebraicGeometry.sigmaMk _).symm (e.inv q), by simp⟩
  rw [AlgebraicGeometry.sigmaMk_mk] at hv
  refine ⟨Sigma.ι (fun _ : Fin n => Spec (.of K)) j ≫ e.hom ≫ pullback.fst p x, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he]
    simp
  · rw [Subsingleton.elim w v, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply]
    simpa using hq₁

theorem existsUnique_section_of_dense (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by
  have hO : ∀ i, IsOpenImmersion (σ i) := fun i => isOpenImmersion_section p (σ i) (hσ i)
  have hCl : ∀ i, IsClosedImmersion (σ i) := fun i => by
    have : IsClosedImmersion (σ i ≫ p) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) p
  have hp : ∀ i s, p (σ i s) = s := fun i s => by
    rw [← Scheme.Hom.comp_apply, hσ i]; rfl

  have hdisj : ∀ i j s s', σ i s = σ j s' → i = j := by
    intro i j s s' hss
    have hE : IsOpen ((σ i).base ⁻¹' Set.range (σ j)) :=
      (σ j).isOpenEmbedding.isOpen_range.preimage (σ i).continuous
    obtain ⟨t, htE, htD⟩ := hD.inter_open_nonempty _ hE ⟨s, s', hss.symm⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h t htD
    obtain ⟨t', ht'⟩ := htE
    have hsec : ((x' ≫ σ i) ≫ p) ≫ σ j = x' ≫ σ i := by
      rw [comp_section_eq_iff p (σ j) (hσ j)]
      exact ⟨t', by rw [Scheme.Hom.comp_apply, hw']; exact ht'⟩
    simp only [Category.assoc] at hsec
    rw [reassoc_of% (hσ i)] at hsec
    have hl : (x' ≫ σ i) ≫ p = x' := by rw [Category.assoc, hσ i, Category.comp_id]
    exact (hu _ hl).unique rfl hsec

  have hcov : ∀ z : Z, ∃ i, z ∈ Set.range (σ i) := by
    by_contra hne
    push Not at hne
    set C : Set Z := (⋃ i, Set.range (σ i))ᶜ with hCdef
    have hCo : IsOpen C :=
      (isClosed_iUnion_of_finite fun i => (σ i).isClosedEmbedding.isClosed_range).isOpen_compl
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀C : z₀ ∈ C := by simpa [hCdef] using hz₀
    obtain ⟨t, ⟨z, hzC, rfl⟩, htD⟩ :=
      hD.inter_open_nonempty _ (p.isOpenMap C hCo) ⟨p z₀, z₀, hz₀C, rfl⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h (p z) htD
    obtain ⟨y', hy'p, hy'w⟩ := exists_lift p x' w' z hw'.symm
    obtain ⟨i, hi, -⟩ := hu y' hy'p
    apply hzC
    rw [Set.mem_iUnion]
    exact ⟨i, x' w', by rw [← hy'w, ← hi, Scheme.Hom.comp_apply]⟩
  let w : Spec (.of K) := default
  obtain ⟨i, hi⟩ := hcov (y w)
  have hyi : (y ≫ p) ≫ σ i = y := (comp_section_eq_iff p (σ i) (hσ i) y w).2 hi
  rw [hy] at hyi
  refine ⟨i, hyi, fun j hj => ?_⟩
  obtain ⟨s, hs⟩ := hi
  refine hdisj j i (x w) s ?_
  rw [hs, ← hj, Scheme.Hom.comp_apply]

theorem comp_linComb {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  let φ : (T ⟶ A) →* (T' ⟶ A) :=
    { toFun := fun g => f ≫ g, map_one' := MonObj.comp_one f, map_mul' := MonObj.comp_mul f }
  have hφ := map_list_prod φ (List.ofFn fun i => y i ^ a i)
  simpa [φ, List.map_ofFn, Function.comp_def, MonObj.comp_pow] using hφ

theorem linComb_pow_eq_one {A T : Over S} [GrpObj A] [IsCommMonObj A] {n k : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ k = 1) (a : Fin n → ℕ) :
    Out.linComb y a ^ k = 1 := by
  unfold Out.linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, hy i, one_pow]

end GlobalTheory.DenseBasis

namespace GlobalTheory

open DenseBasis LatticeTorsion in

theorem torsion_basis_of_dense :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A)) (Sg : Set S), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → (∀ i, pt i ^ k = 1) → Dense Sg → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ ∀ y : Over.mk x ⟶ A, y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y := by
  intro S A _ k r pt Sg hA hk hku hpt hD hSg K _ _ x y hy
  have : IsCommMonObj A := hA.comm
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨Z, et, hZf, hZe, hadd, hkill, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom S A k ℤ hA hku
  have := hZf
  have := hZe

  have het : ∀ m : ℤ, et m = et 1 ^ m := by
    have h0 : et 0 = 1 := by
      have h00 := hadd 0 0
      rw [add_zero] at h00
      exact left_eq_mul.mp h00
    intro m
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ n ih => rw [hadd, ih, zpow_add_one]
    | pred n ih =>
      have hn := hadd (-(n : ℤ) - 1) 1
      rw [sub_add_cancel, ih] at hn
      rw [zpow_sub_one, hn, mul_inv_cancel_right]

  have hfac : ∀ (T : Over S) (a : T ⟶ A), a ^ k = 1 → ∃! g : T ⟶ Z, g ≫ et 1 = a := by
    intro T a ha
    obtain ⟨g, hg, hgu⟩ := huniv T (fun m => a ^ m) (fun m c => zpow_add a m c) (fun m => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow])
    refine ⟨g, by simpa using hg 1, fun g' hg' => hgu g' fun m => ?_⟩
    rw [het m, GrpObj.comp_zpow, hg']
  have hktor : ∀ (T : Over S) (g : T ⟶ Z), (g ≫ et 1) ^ k = 1 := fun T g => by
    rw [← MonObj.comp_pow, hkill 1, MonObj.comp_one]

  have hP : ∀ c : Fin r → ZMod k, Out.linComb pt (fun i => (c i).val) ^ k = 1 :=
    fun c => linComb_pow_eq_one pt hpt _
  choose h hh using fun c => (hfac _ _ (hP c)).exists
  have hsec : ∀ c, (h c).left ≫ Z.hom = 𝟙 S := fun c => by
    rw [Over.w (h c)]
    rfl
  have key : ∀ (K' : Type) [Field K'] (x' : Sp K' ⟶ S) (Y' : Over.mk x' ⟶ Z)
      (c : Fin r → ZMod k),
      Out.linComb (fun i => (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (c i).val) = Y' ≫ et 1 ↔ x' ≫ (h c).left = Y'.left := by
    intro K' _ x' Y' c
    rw [← comp_linComb, ← hh c, ← Category.assoc]
    constructor
    · intro he
      have he' := (hfac _ (Y' ≫ et 1) (hktor _ Y')).unique he rfl
      rw [← he']
      simp
    · intro he
      have he' : (Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver S) ≫ h c = Y' := by
        ext
        simpa using he
      rw [he']
  have hdense : ∀ t ∈ Sg, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K')
      (x' : Spec (.of K') ⟶ S), t ∈ Set.range x' ∧
        ∀ y' : Spec (.of K') ⟶ Z.left, y' ≫ Z.hom = x' →
          ∃! c, x' ≫ (fun c => (h c).left) c = y' := by
    intro t ht
    obtain ⟨K', _, _, x', hx', H⟩ := hSg t ht
    refine ⟨K', inferInstance, inferInstance, x', hx', fun y' hy' => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := H _ (hktor _ (Over.homMk y' hy' : Over.mk x' ⟶ Z))
    exact ⟨c, (key K' x' _ c).1 hc1, fun c' hc' => hc2 c' ((key K' x' _ c').2 hc')⟩
  obtain ⟨Y', hY', -⟩ := hfac (Over.mk x) y hy
  obtain ⟨c, hc1, hc2⟩ := existsUnique_section_of_dense Z.hom (fun c => (h c).left) hsec Sg hD
    hdense K x Y'.left (by simp [Over.w Y'])
  refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
  · rw [← hY']
    exact (key K x Y' c).2 hc1
  · rw [← hY'] at hc'
    exact (key K x Y' c').1 hc'

end GlobalTheory
end

