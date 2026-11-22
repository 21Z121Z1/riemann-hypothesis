import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibres

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NearCOfPolFamOfKTriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem nearC_of_polFam_of_kTriv : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Ideal.span (Set.range v) = ⊤ → PolFam b Mat κ β v A L act Q → Out.KTriv A L → NearC b Mat κ β v q₀ := by
  intro h1 h2 g n j J hn hodd hj o _ b Mat κ R _ _ _ β v A _ L act Q q₀ hD hv hP hK
  obtain ⟨hD1, hD2⟩ := hD
  obtain ⟨hAb, hdim, hLB, hrig, hsym, hamp, hlab, hgood⟩ := hP
  obtain ⟨hl1, hl2, hl3⟩ := hlab
  let P : Out.PolAV (Sp R) :=
    { A := A, isAb := hAb, g := g, smoothDim := hdim, L := L, isLB := hLB, rigid := hrig, sym := hsym,
      ample := hamp, ktriv := hK }
  have hpos : 0 < n ^ j := pow_pos hn.pos j

  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, ⟨hpb₁, hL₁, hact₁, hpt₁⟩, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_level_cover h1 h2 o g (n ^ j) J b R β P act Q hpos ⟨rfl, hl1, hl2, hl3⟩
  have hG₁ : GLies A act Q (spMap (algebraMap R R₁)) t₁ ψ₁ := And.intro hpb₁ (And.intro hact₁ hpt₁)
  have h3 : 3 ≤ n ^ j := by
    have := Nat.odd_iff.1 hodd
    have := hn.two_le
    have : n ≤ n ^ j := Nat.le_self_pow (by omega) n
    omega

  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff h1 h2 o g (n ^ j) J b R₁
    (spMap (algebraMap R R₁) ≫ spMap β) t₁ (fun a => algebraMap R R₁ (v a)) hodd.pow h3
    (GlobalTheory.ThetaClosed.span_map_eq_top (algebraMap R R₁) hv)

  have kill : ∀ (K : Type) [Field K] (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (y₁ : R₁ →+* K), y₁.comp (algebraMap R R₁) = x → TMap t t₁ (spMap y₁) →
      t.HasTh (𝟙 _) (fun a => x (v a)) → ∀ r ∈ 𝔞, y₁ r = 0 := by
    intro K _ x t y₁ hc hT hth
    apply (h𝔞 K y₁).1
    have h := (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp K) _ t (spMap y₁) K (𝟙 _) (fun a => x (v a)) hT).1 hth
    rw [Category.id_comp] at h
    have hw : (fun a => x (v a)) = fun a => y₁ (algebraMap R R₁ (v a)) := by
      funext a; rw [← hc]; rfl
    rw [hw] at h
    exact h

  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = y'.comp (algebraMap R R₁) →
      (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) → y = y' := by
    intro K _ _ y y' hyy hy hy'
    have th := (h𝔞 K y).2 hy
    have th' := (h𝔞 K y').2 hy'
    have hw : (fun a => y' (algebraMap R R₁ (v a))) = fun a => y (algebraMap R R₁ (v a)) := by
      funext a; exact (RingHom.congr_fun hyy (v a)).symm
    have hc : spMap y ≫ spMap (algebraMap R R₁) = spMap y' ≫ spMap (algebraMap R R₁) := by
      rw [← spMap_comp, ← spMap_comp, hyy]
    have heq := level_eq_of_gLies_of_hasTh h1 h2 g n j J hn hodd hj o b (Sp R) (Sp R₁) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ K (spMap y) (spMap y')
      (fun a => y (algebraMap R R₁ (v a))) hLB hG₁ hL₁ hc
      (by rw [← Category.assoc, ← Category.assoc, hc]) th (by rw [← hw]; exact th')
    obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y)
      (spMap (y.comp (algebraMap R R₁)) ≫ spMap β) hLB hG₁ hL₁
      (by rw [spMap_comp, Category.assoc])
    have hc' : spMap y' ≫ spMap (algebraMap R R₁) = spMap (y.comp (algebraMap R R₁)) := by
      rw [← hc, spMap_comp]
    have hGu' : GLies A act Q (spMap (y.comp (algebraMap R R₁))) u ψ := by
      have ⟨g1, g2, g3⟩ := hGu
      rw [← spMap_comp y (algebraMap R R₁)] at g1 g3
      exact And.intro g1 (And.intro g2 g3)
    have hTu' : TMap u t₁ (spMap y') := tmap_of_glies o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y') _ u ψ hLB hG₁ hL₁
      (by rw [hc']; exact hGu') hLu (fun i => (hptu i).trans (heq i))
    have ⟨hg1, hg2, hg3⟩ := hGu'
    obtain ⟨y₀, -, huq⟩ := huniv K (y.comp (algebraMap R R₁)) u ψ ⟨hg1, hLu, hg2, hg3⟩
    exact (huq y ⟨rfl, hptu, hTu⟩).trans (huq y' ⟨hyy.symm, fun i => (hptu i).trans (heq i), hTu'⟩).symm
  have hqa : algebraMap R (R₁ ⧸ 𝔞) = (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) :=
    IsScalarTower.algebraMap_eq R R₁ (R₁ ⧸ 𝔞)
  have : Module.Finite R (R₁ ⧸ 𝔞) := Module.Finite.trans R₁ (R₁ ⧸ 𝔞)
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) := inferInstance

  have hup : ∀ q ∈ objPrimes b Mat κ β v, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : R₁ ⧸ 𝔞 →+* K, y.comp (algebraMap R (R₁ ⧸ 𝔞)) = x := by
    intro q hq
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    obtain ⟨ψ, hG, hLψ⟩ := hgood K x _ t (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K x t ψ ⟨hg1, hLψ, hg2, hg3⟩
    have hk := kill K x t y₁ hy₁c hy₁T hth
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y₁ hk, ?_, ?_⟩
    · beta_reduce
      rw [hqa, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hy₁c]
    · intro y hy
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.Quotient.lift_comp_mk]
      apply key K (y.comp (Ideal.Quotient.mk 𝔞)) y₁
      · rw [RingHom.comp_assoc, ← hqa, hy, hy₁c]
      · intro r hr
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      · exact hk

  obtain ⟨f, hfq, r, hr, -⟩ := exists_retraction_near_of_unique_point R (R₁ ⧸ 𝔞)
    (objPrimes b Mat κ β v) hD1 hup q₀ hD2
  obtain ⟨z, hzdef⟩ : ∃ z : R₁ →+* Localization.Away f, z = r.comp (Ideal.Quotient.mk 𝔞) := ⟨_, rfl⟩
  have hz : z.comp (algebraMap R R₁) = loc f := by
    rw [hzdef, RingHom.comp_assoc, ← hqa, hr]
  have hzk : ∀ x ∈ 𝔞, z x = 0 := by
    intro x hx
    rw [hzdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

  obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁)
    (Sp (Localization.Away f)) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β)
    t₁ ψ₁ (spMap z) (spMap ((loc f).comp β)) hLB hG₁ hL₁
    (by rw [← hz, spMap_comp (z.comp (algebraMap R R₁)) β, spMap_comp z (algebraMap R R₁), Category.assoc])
  refine Exists.intro f (And.intro hfq (Exists.intro u (And.intro ?_ ?_)))
  · have h := (h𝔞 _ z).2 hzk
    apply (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp (Localization.Away f)) _ u (spMap z) (Localization.Away f) (𝟙 _) (fun a => loc f (v a)) hTu).2
    rw [Category.id_comp]
    have hw : (fun a => loc f (v a)) = fun a => z (algebraMap R R₁ (v a)) := by
      funext a; rw [← hz]; rfl
    rw [hw]; exact h
  · intro K _ _ x s t' hg
    obtain ⟨rfl, hsh, hth⟩ := (good_comp (loc f) x t').1 hg
    obtain ⟨ψ', hG', hLψ'⟩ := hgood K (x.comp (loc f)) _ t' (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG'
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K (x.comp (loc f)) t' ψ' ⟨hg1, hLψ', hg2, hg3⟩
    have hk := kill K (x.comp (loc f)) t' y₁ hy₁c hy₁T hth
    have hyz : y₁ = x.comp z := key K y₁ (x.comp z) (by rw [hy₁c, RingHom.comp_assoc, hz]) hk
      (by intro r' hr'; rw [RingHom.comp_apply, hzk r' hr', map_zero])
    rw [hyz, spMap_comp x z] at hy₁T
    exact TMap.cancel hTu hy₁T

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SerreLemmaSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace SerreLemma

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_lift {X Y : Over (Sp k)} (m : X ⟶ Y) [LocallyOfFiniteType m.left]
    (x : 𝟙_ (Over (Sp k)) ⟶ Y) (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range m.left) :
    ∃ a : 𝟙_ (Over (Sp k)) ⟶ X, a ≫ m = x := by
  let x' : Spec (CommRingCat.of k) ⟶ Y.left := x.left
  have hJ : JacobsonSpace ↥(pullback m.left x') :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd m.left x')
  obtain ⟨w, hw⟩ := hx
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := m.left) (g := x') w _ hw
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback m.left x')))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  have e : (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ≫ m.left = x' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ?_,
    Over.OverMorphism.ext e⟩
  rw [← Over.w m, ← Category.assoc, e]
  exact Over.w x

theorem exists_pow_eq (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) (n : ℕ) (hn : (n : k) ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ n = x := by
  have := hG.comm
  have := hG.smooth
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have := GrpTangent.etale_mulN G hu
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range (mulN G n).left with hU
  have hUo : IsOpen U := (mulN G n).left.isOpenMap.isOpen_range
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k) ∈ U := by
    refine ⟨(1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun z : 𝟙_ (Over (Sp k)) ⟶ G => z.left (IsLocalRing.closedPoint k))
      (MonObj.one_comp (mulN G n))
  have hVo : IsOpen ((GrpObj.mulRight x).hom.left ⁻¹' U) := hUo.preimage (Scheme.Hom.continuous _)
  have hV : ((GrpObj.mulRight x).hom.left ⁻¹' U).Nonempty := by
    refine ⟨(x⁻¹).left (IsLocalRing.closedPoint k), ?_⟩
    rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply, inv_mul_cancel]
    exact hone
  obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hUo hVo ⟨_, hone⟩ hV) (hUo.inter hVo).isLocallyClosed
  obtain ⟨z, rfl⟩ := OpenSubgroupScheme.exists_point y hyc
  rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply] at hyV
  obtain ⟨a, ha⟩ := exists_lift _ z hyU
  obtain ⟨b, hb⟩ := exists_lift _ _ hyV
  rw [GrpTangent.comp_mulN] at ha hb
  refine ⟨a⁻¹ * b, ?_⟩
  rw [mul_pow, inv_pow, ha, hb, inv_mul_cancel_left]

end SerreLemma

theorem serre_lemma_semiAbelian : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ (N r : ℕ) (u : Aut G), Odd N → 3 ≤ N → (N : k) ≠ 0 → 0 < r → IsMonHom u.hom → u ^ r = 1 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, x ^ N = 1 → x ≫ u.hom = x) → u = 1 := by
  intro k _ _ G _ hG N r u hodd h3 hN hr hu hur hfix
  have := hG.comm
  obtain ⟨l, hl, hlN⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
  have hlo : Odd l := Odd.of_dvd_nat hodd hlN
  have hlk : (l : k) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hlN
    rw [Nat.cast_mul] at hN
    exact left_ne_zero_of_mul hN
  let e : (𝟙_ (Over (Sp k)) ⟶ G) ≃* (𝟙_ (Over (Sp k)) ⟶ G) :=
    { toFun x := x ≫ u.hom
      invFun x := x ≫ u.inv
      left_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.hom_inv_id).trans (Category.comp_id x))
      right_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.inv_hom_id).trans (Category.comp_id x))
      map_mul' x y := MonObj.mul_comp x y u.hom }
  have hit : ∀ (n : ℕ) x, e^[n] x = x ≫ (u ^ n).hom := by
    intro n
    induction n with
    | zero => intro x; exact (Category.comp_id x).symm
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ', Aut.Aut_mul_def]
      exact Category.assoc x (u ^ n).hom u.hom
  have key := minkowski_divisible _ l e r hl hlo hr (SerreLemma.exists_pow_eq G hG l hlk)
    (fun x => by rw [hit, hur]; exact Category.comp_id x)
    (fun x hx => hfix x (by obtain ⟨c, rfl⟩ := hlN; rw [pow_mul, hx, one_pow]))
  have hm : IsMonHom (u.hom * (𝟙 G)⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        rw [mul_eq_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, MonObj.mul_comp,
          MonObj.comp_mul, mul_inv, _root_.mul_mul_mul_comm]
        congr 1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one k G G hG hG l hl hlk (u.hom * (𝟙 G)⁻¹) hm (fun _ _ y a hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
    exact mul_inv_eq_one.mpr (key y a hy))
  exact Iso.ext (mul_inv_eq_one.mp h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  first | exact @GlobalTheory.ZM.WFam.qproj_flat_reduced_ext | exact GlobalTheory.ZM.WFam.qproj_flat_reduced_ext | (intros; apply GlobalTheory.ZM.WFam.qproj_flat_reduced_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.KTrivSpread

theorem kTriv_of_finite_flat {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A : Over (Sp V)} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {Z : Over (Sp V)} (i : Z ⟶ A)
    [IsFinite Z.hom] [Flat Z.hom]
    (hZ : ∀ (T : Over (Sp V)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x)
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ)
    {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hk : KTriv A' L') : KTriv A L := by
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  let Y := pullback Z.hom (spMap (algebraMap V K))
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.snd Z.hom (spMap (algebraMap V K)))
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let d : Sp Γ(Y, ⊤) ⟶ Z.left := Y.isoSpec.inv ≫ pullback.fst Z.hom (spMap (algebraMap V K))
  let t : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd Z.hom (spMap (algebraMap V K))
  have hd : d ≫ Z.hom = t ≫ spMap (algebraMap V K) := by
    simp only [d, t, Category.assoc, pullback.condition]
  have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap (algebraMap V K) := by
    rw [Category.assoc, Over.w i, hd]
  let x : Over.mk t ⟶ A' := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
  let z : Over.mk (t ≫ spMap (algebraMap V K)) ⟶ Z := Over.homMk d hd
  have hz : z ≫ i = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
  have hx : x = 1 := hk _ t x (memKL_of_push h hL hL' hw x ((hZ _ _).2 ⟨z, hz⟩))
  have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
  have hi : i = toUnit Z ≫ η[A] := by
    have : IsSchemeTheoreticallyDominant d := by
      dsimp only [d]; infer_instance
    refine over_ext_of_schemeTheoreticallyDominant d (congrArg (fun q => q.left)
      (show z ≫ i = z ≫ toUnit Z ≫ η[A] from ?_))
    rw [hz, hx', ← Category.assoc, comp_toUnit]
    rfl
  intro R _ s y hy
  obtain ⟨u, rfl⟩ := (hZ _ y).1 hy
  rw [hi, ← Category.assoc, comp_toUnit]

theorem kTriv_of_generic_fibre : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  intro hL V K _ _ _ _ _ _ P B _ _ M φ hB h hw ha
  have hM := M.L.isLB
  have hP : AbLaw.IsProjBy B.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B M.L.L hB hM ha V (𝟙 _) B.left (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨hO, hu, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ B M.L.L hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V B hB hP M.L.L _ hM hO
  have hfin : IsFinite H.hom :=
    AmpleStabFinite.isFinite_of_relAmple hL.globalFns V B hB M.L.L _ hM hO ha H j hj hH
  have hflat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V B hB hP M.L M.c _ hO hu H j hj hH hfin
  exact kTriv_of_finite_flat hB hM j (fun T x => (hK _ rfl T x).trans (hH T x)) h P.isLB hw P.ktriv

end GlobalTheory.KTrivSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  first | exact @GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | exact GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | (intros; apply GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  first | exact @GlobalTheory.SpreadLevel.main | exact GlobalTheory.SpreadLevel.main | (intros; apply GlobalTheory.SpreadLevel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (m : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (t t' : TObj g (N' ^ 2) J b (spMap β)), 2 ≤ m → m ^ 2 ∣ N' → Odd N' → Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (u : TObj g (N' ^ 2) J b (x ≫ spMap β)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} → TMap t t' (𝟙 _) ∧ ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A (𝟙 _) φ → IsGrpPullback t.A t'.A (𝟙 _) φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  first | exact @GlobalTheory.TUniq.iso_unique_of_dense | exact GlobalTheory.TUniq.iso_unique_of_dense | (intros; apply GlobalTheory.TUniq.iso_unique_of_dense <;> assumption)
end

