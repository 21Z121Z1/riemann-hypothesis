import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_point_of_inter {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (i : V →+* K) (j : V →+* O) (k : K →+* C) (l : O →+* C) (hi : Function.Injective i) (hl : Function.Injective l)
    (hc : ∀ v, l (j v) = k (i v)) (hint : ∀ (a : K) (c : O), k a = l c → ∃ v, i v = a)
    {X : Scheme.{0}} (x : Sp K ⟶ X) (b : Sp O ⟶ X) (h : spMap k ≫ x = spMap l ≫ b) :
    ∃ y : Sp V ⟶ X, spMap i ≫ y = x ∧ spMap j ≫ y = b := by
  obtain ⟨U, hU, hb, -⟩ := exists_isAffineOpen_le b (le_preimage_top b)
  have hlb : ⊤ ≤ (spMap l ≫ b) ⁻¹ᵁ U := le_preimage_comp _ b hb (le_preimage_top _)
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ (spMap k ≫ x) ⁻¹ᵁ U := h ▸ hlb
    intro w _
    rw [Subsingleton.elim w (spMap k (IsLocalRing.closedPoint C))]
    exact h1 (x := IsLocalRing.closedPoint C) trivial
  have hv : ∀ f, k ((valMap x U hx).hom f) = l ((valMap b U hb).hom f) := fun f => by
    rw [← valR_eq, ← valR_eq, ← valR_spMap_comp k x U hx, ← valR_spMap_comp l b U hb, h]
  choose g hg using fun f => hint _ _ (hv f)
  let ψ : Γ(X, U) →+* V :=
    { toFun := g
      map_one' := hi (by simp only [hg, map_one])
      map_mul' := fun a c => hi (by simp only [hg, map_mul])
      map_zero' := hi (by simp only [hg, map_zero])
      map_add' := fun a c => hi (by simp only [hg, map_add]) }
  have e1 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom i = valMap x U hx := by
    ext f
    exact hg f
  have e2 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom j = valMap b U hb := by
    ext f
    exact hl ((hc _).trans ((congrArg k (hg f)).trans (hv f)))
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e1, specMap_valMap_fromSpec]
  · rw [← Category.assoc, ← Spec.map_comp, e2, specMap_valMap_fromSpec]

theorem pushHom_inj_of_cartesian {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := fun a b e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))

theorem torsion_integral_descends : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u jV hj b hb
  haveI := u.U.gen_hom
  let k : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  have hsq : gPt p ≫ spMap jV = spMap k ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => spMap φ) (RingHom.ext hj)
  have hbw : b.left ≫ u.G.hom = spMap jV := Over.w b
  let T : Over (Sp (FractionRing u.V)) := Over.mk (spMap k)
  let wl : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (gPt p ≫ b.left) (spMap k) (by rw [Category.assoc, hbw, hsq])
  have w1 : wl ≫ pullback.fst _ _ = gPt p ≫ b.left := pullback.lift_fst _ _ _
  have w2 : wl ≫ pullback.snd _ _ = spMap k := pullback.lift_snd _ _ _
  let w : T ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk wl w2
  let W : Over.mk (T.hom ≫ jK u.V) ⟶ Over.mk (spMap jV) := Over.homMk (gPt p) hsq
  have hp := isGrpPullback_pullback u.G (jK u.V)
  have e0 : pushHom hp T w = preHom W b := Over.OverMorphism.ext w1
  have hw : w ^ (S.r * S.N) = 1 := pushHom_inj_of_cartesian hp T (by
    rw [map_pow, e0, ← map_pow, hb, map_one, map_one])
  have hw' : (w ≫ u.U.gen.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (T.hom ≫ spMap u.yK) (pushHom u.cart T (w ≫ u.U.gen.hom))
    (by rw [← map_pow, hw', map_one])
  have ha' : (spMap k ≫ spMap u.yK) ≫ (ρ.pt a).left = (wl ≫ u.U.gen.hom.left) ≫ u.φ :=
    congrArg (fun z => z.left) ha
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hg : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd _ _ := Over.w u.U.gen.hom
  have hg' : u.U.gen.inv.left ≫ pullback.snd _ _ = u.A.A.hom := Over.w u.U.gen.inv
  have hih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.inv_hom_id
  have hhi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.hom_inv_id
  obtain ⟨x', x1, x2⟩ : ∃ x' : Sp (FractionRing u.V) ⟶ u.A.A.left,
      x' ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ x' ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa, Category.id_comp]; exact Category.comp_id _), u.cart.1.lift_fst _ _ _,
      u.cart.1.lift_snd _ _ _⟩
  have hx' : spMap k ≫ x' = wl ≫ u.U.gen.hom.left := by
    refine u.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, x1, ← Category.assoc]
      exact ha'
    · rw [Category.assoc, x2, Category.comp_id, Category.assoc]
      exact ((congrArg (wl ≫ ·) hg).trans w2).symm
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) := x' ≫ u.U.gen.inv.left
  have hx : spMap k ≫ x = wl := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.U.gen.inv.left) hx').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (wl ≫ ·) hhi).trans (Category.comp_id _))
  have hxs : x ≫ pullback.snd _ _ = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hg').trans x2)
  obtain ⟨hV, h1, h2⟩ := exists_point_of_inter (algebraMap u.V (FractionRing u.V)) jV k (OO p).subtype
    (IsFractionRing.injective _ _) Subtype.val_injective hj
    (fun a c e => (u.norm_le a).1 ((mem_OO_iff _).1 (by
      have e' : algebraMap _ (PadicAlgCl p) a = c := e
      rw [e']; exact c.2)))
    (x ≫ pullback.fst _ _) b.left (by rw [← Category.assoc, hx, w1])
  refine ⟨a, hV, x, ⟨?_, h1.symm, hxs, ?_⟩, h2⟩
  · rw [← Spec.map_preimage (hV ≫ u.G.hom), ← Spec.map_id]
    congr 1
    have h3 : Spec.preimage (hV ≫ u.G.hom) ≫ CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) =
        CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
      refine (congrArg (· ≫ u.G.hom) h1).trans ?_
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, Category.id_comp]
    ext v
    exact IsFractionRing.injective u.V (FractionRing u.V) (congrArg (fun φ => φ.hom v) h3)
  · refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (x' ≫ ·) ?_) x1)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) hih).trans (Category.id_comp _))

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SpanImm

theorem closure_eq_top_iff {A B J : Type} [CommRing A] [CommRing B] (c : A →+* B) (r : J → B) :
    Subring.closure (Set.range c ∪ Set.range r) = ⊤ ↔
      Function.Surjective (MvPolynomial.eval₂Hom c r) := by
  rw [← RingHom.range_eq_top]
  suffices h : Subring.closure (Set.range c ∪ Set.range r) = (MvPolynomial.eval₂Hom c r).range by
    rw [h]
  refine le_antisymm (Subring.closure_le.2 ?_) ?_
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  · rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem range_constFn {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) :
    Set.range (constFn p U) = Set.range (p.appLE ⊤ U le_top).hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact hs.range_comp (p.appLE ⊤ U le_top).hom

theorem immBy_iff {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) : ImmBy p H s Set.univ ↔ AmpleSpan.EmbedsBy p s := by
  unfold ImmBy AmpleSpan.EmbedsBy
  simp only [Set.mem_univ, iSup_pos, forall_true_left, range_constFn, closure_eq_top_iff]
  rfl

theorem immBy_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  intro k _ X p _ H _ I J _ _ t s ht hs
  refine (immBy_iff p H s).2 (((immBy_iff p H t).1 ht).of_inSpan fun i => ?_)
  obtain ⟨a, ha⟩ := hs i
  exact ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (a j), ha⟩

end GlobalTheory.ZH.SpanImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}
  {J : Type} {σ : J → H.Sec} {t : J → Ω}

theorem mem_nonzeroLocus_iff_div (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hg : ∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) (i : J) (z : M.Z) :
    z ∈ Out.nonzeroLocus (σ i) ↔ M.Div t i z := by
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
    obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
    have e := hv i l ⟨z, hzl⟩
    dsimp only at h0 h1
    rw [e] at h0 h1
    have hi : t i ≠ 0 := fun h => h0 (by rw [h, zero_div])
    refine ⟨hi, fun j => ?_⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (t i / d l)⁻¹ = t j / t i := by field_simp
    rwa [e'] at h3
  · intro hz
    have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i', hi', h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 ((isUnit_O_iff _).2 ?_)⟩
    dsimp only
    rw [hv i l ⟨z, hzl⟩]
    refine ⟨div_ne_zero hz.1 (hd.ne l), ?_⟩
    have h3 := mul_mem h1 (hz.2 i')
    have hi := hz.1
    have e' : d l / t i' * (t i' / t i) = (t i / d l)⁻¹ := by field_simp
    rwa [e'] at h3

theorem immBy_of_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  intro o Ω _ _ _ M H d J σ t k _ p ψ hH hd hv hg hp hU
  have key := mem_nonzeroLocus_iff_div hH hd hv hg
  refine ⟨top_unique fun z _ => ?_, fun i _ => ?_⟩
  · have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i, hi, h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨trivial, (key i z).2 ⟨hi, fun j => ?_⟩⟩⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (d l / t i) = t j / t i := by field_simp
    rwa [e'] at h3
  · have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
      have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
      subst this
      infer_instance
    have key' := key i
    generalize Out.nonzeroLocus (σ i) = W at key' ⊢
    by_cases hi : t i = 0
    · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
      subst hW
      refine ⟨isAffineOpen_bot _, fun _ => 0, fun j l => ?_,
        top_unique fun f _ => Subsingleton.elim 0 f ▸ zero_mem _⟩
      have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
      exact Subsingleton.elim _ _
    · obtain ⟨U, hUa, hUe, hR⟩ := hU i hi
      have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
      subst hWU
      have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
      have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
        (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
      choose r hr using hr
      refine ⟨hUa, r, fun j l => ?_, ?_⟩
      · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
        · have hl' : (H.U l : Set M.Z).Nonempty := hl.mono fun z hz => hz.2
          apply M.res_injective _ hl
          rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
            hv j l hl', hv i l hl', hr]
          have hdl := hd.ne l
          field_simp
        · have := hempty _ hl
          exact Subsingleton.elim _ _
      · refine top_unique fun f _ => ?_
        have h1 := hR _ ((mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩)
        have e : (Set.range ψ ∪ Set.range fun j => t j / t i) =
            M.res W hne '' (Set.range (constFn p W) ∪ Set.range r) := by
          rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
          congr 2
          · funext a
            exact ((M.res_apply W hne _).trans
              (valR_constFn_of_over p ψ M.pt hp W (M.top_le_preimage_pt hne) a)).symm
          · funext j
            exact ((M.res_apply W hne _).trans (hr j)).symm
        rw [e, ← RingHom.map_closure] at h1
        obtain ⟨g, hg1, hg2⟩ := h1
        have : g = f := M.res_injective W hne (hg2.trans (M.res_apply W hne f).symm)
        exact this ▸ hg1

end GlobalTheory.ZH.RatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGeneratorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLinComb_iff_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  first | exact @GlobalTheory.ZH.UFib.isLin_iff_of_red | exact GlobalTheory.ZH.UFib.isLin_iff_of_red | (intros; apply GlobalTheory.ZH.UFib.isLin_iff_of_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem isLocalHom_of_test {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p)
    (hj : ∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) :
    IsLocalHom jV := by
  refine ⟨fun x hx => ?_⟩
  have h1 : ‖(jV x : PadicAlgCl p)‖ = 1 :=
    le_antisymm ((mem_OO_iff _).1 (jV x).2) (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hx)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by
    rw [hj, h, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) x)⁻¹).1 (by
    rw [map_inv₀, ← hj, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, mul_inv_cancel₀ h0, map_one]

end GlobalTheory.ZH.ZHPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitOfVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {X Y : Scheme.{0}} {K : Type} [Field K]

theorem le_inf' {g : Sp K ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem le_wchart {I : Type} [Fintype I] (L : LB X) (φ : Y ⟶ X) (j : I → L.ι) {g : Sp K ⟶ Y}
    (h : ∀ i, ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i)) : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j :=
  fun _ hz => Set.mem_iInter.2 fun i => h i hz

theorem of_le_wchart {I : Type} [Fintype I] {L : LB X} {φ : Y ⟶ X} {j : I → L.ι} {g : Sp K ⟶ Y}
    (h : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j) (i : I) : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i) :=
  fun _ hz => Set.mem_iInter.1 (h hz) i

noncomputable def vU (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : Γ(X, U)ˣ →* Kˣ :=
  Units.map (valMap g U h).hom.toMonoidHom

theorem vU_val (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF g U u.val = (vU g U h u).val := valR_eq g U h _

theorem val_unit_ne (g : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : valF g U u.val ≠ 0 := by
  rw [vU_val g U h]; exact Units.ne_zero _

theorem val_junk (g : Sp K ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) : valF g U f = 0 := dif_neg h

theorem val_linComb_g {I : Type} [Fintype I] [Unique I] (L : LB X) (φ : Y ⟶ X) (n : ℤ) (a b : L.ι) (g : Sp K ⟶ Y)
    (ha : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U b) :
    valF g _ ((LB.LinComb L (K := I) (fun _ => φ) (fun _ => n)).g (fun _ => a) (fun _ => b)).val =
      valF (g ≫ φ) _ (L.g a b).val ^ n := by
  have h := le_inf' (le_wchart L φ (fun _ : I => a) fun _ => ha) (le_wchart L φ (fun _ : I => b) fun _ => hb)
  have key : ∀ (W : Y.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ φ ⁻¹ᵁ (L.U a ⊓ L.U b)),
      valF g W (∏ _k : I, res e (pullU φ _ (L.g a b)) ^ n).val = valF (g ≫ φ) _ (L.g a b).val ^ n := fun W h e => by
    rw [vU_val g _ h, Fintype.prod_unique, map_zpow, Units.val_zpow_eq_zpow_val, ← vU_val]
    rw [GlobalTheory.NormGlue.val_res_pullU]
    exact congrArg (· ^ n) (valR_appLE g φ e h _)
  exact key (LB.wchart L (fun _ : I => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : I => φ) (fun _ => b)) h
    (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => a) default))
      (inf_le_right.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => b) default)))

theorem val_div_g (M L : LB X) (a b : (LB.div M L).ι) (g : Sp K ⟶ X)
    (ha : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U a) (hb : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U b) :
    valF g _ ((LB.div M L).g a b).val = valF g _ (M.g a.1 b.1).val * (valF g _ (L.g a.2 b.2).val)⁻¹ := by
  have h := le_inf' ha hb
  have key : ∀ (W A B : X.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ A) (e' : W ≤ B) (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ),
      valF g W (res e u * (res e' v)⁻¹).val = valF g A u.val * (valF g B v.val)⁻¹ := fun W A B h e e' u v => by
    rw [vU_val g _ h, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← vU_val, ← vU_val]
    exact congrArg₂ (fun x y => x * y⁻¹) (valR_res g e h _) (valR_res g e' h _)
  exact key _ _ _ h _ _ _ _

theorem val_sec {H : LB X} (s : LB.Sec H) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.f j) = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.f k) := by
  have h := le_inf' hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem val_gen {H : LB X} {s : LB.Gen H} (hs : s.IsGen) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.s j).val = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.s k).val :=
  val_sec ⟨fun i => (s.s i).val, fun i j => congrArg Units.val (hs i j)⟩ x hj hk

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp K ⟶ X) {k : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valF x _ (L.g k k).val = 1 :=
  (valR_res x _ h _).symm.trans ((congrArg (fun u : Γ(X, L.U k)ˣ => valR x _ u.val) (hL.g_self k)).trans
    (valR_one x _ h))

theorem isUnit_of_val {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (g : Sp K ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valF g U f ≠ 0) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (X.mem_basicOpen f x hx).1 ?_
  let g : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun w _ => show g w ∈ U by rw [hg]; exact hx
  have := (le_preimage_basicOpen_iff g h1 f).2 (h _ g h1).isUnit (x := IsLocalRing.closedPoint _) trivial
  exact Set.mem_of_eq_of_mem (hg _).symm this

def Reg (y : Y) (F : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K) : Prop :=
  ∃ (V : Y.Opens) (f : Γ(Y, V)), y ∈ V ∧ ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → valF g V f = F K g

section
variable {y : Y} {F F' : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}

theorem Reg.val (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ U) : Reg y fun _ _ g => valF (g ≫ m) U s :=
  ⟨m ⁻¹ᵁ U, (m.app U).hom s, h, fun _ _ g _ => (valR_comp g m U s).symm⟩

theorem Reg.inv (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ X.basicOpen s) :
    Reg y fun _ _ g => (valF (g ≫ m) U s)⁻¹ := by
  obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨m ⁻¹ᵁ X.basicOpen s, (m.app _).hom (u⁻¹).val, h, fun _ _ g hg => (valR_comp g m _ _).symm.trans ?_⟩
  replace hg : ⊤ ≤ (g ≫ m) ⁻¹ᵁ X.basicOpen s := hg
  refine (vU_val (g ≫ m) _ hg _).trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val, ← vU_val, hu]
  exact congrArg (·⁻¹) (valR_res _ _ hg _)

theorem Reg.mul (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g * F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f * resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_mul g _ hg _ _).trans (congrArg₂ (· * ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.add (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g + F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f + resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_add g _ hg _ _).trans (congrArg₂ (· + ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.pow (h : Reg y F) (n : ℕ) : Reg y fun K _ g => F K g ^ n := by
  obtain ⟨V, f, hy, hf⟩ := h
  exact ⟨V, f ^ n, hy, fun K _ g hg => (valR_pow g _ hg _ _).trans (congrArg (· ^ n) (hf K g hg))⟩

theorem Reg.sum {I : Type} (s : Finset I) {F : I → ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}
    (h : ∀ i, Reg y (F i)) : Reg y fun K _ g => ∑ i ∈ s, F i K g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, 0, trivial, fun K _ g hg => valR_zero g _ hg⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

end

theorem exists_glue [IsIntegral Y] (V : Y.Opens) (R : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K → Prop)
    {F : Type} [Field F] (ξ : Sp F ⟶ Y) (hξ : ∀ w, ξ w = genericPoint Y)
    (hu : ⊤ ≤ ξ ⁻¹ᵁ V → ∀ v v', R F ξ v → R F ξ v' → v = v')
    (hl : ∀ y ∈ V, ∃ (W : Y.Opens) (f : Γ(Y, W)), y ∈ W ∧
      ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ W → ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g W f)) :
    ∃ f : Γ(Y, V), ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g V f) := by
  choose W f hy hf using fun y : V => hl y.1 y.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun y : V => V ⊓ W y) V (fun y => homOfLE inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hy _⟩) (fun y => resG Y inf_le_right (f y))
    (fun a b => eq_of_valF_generic ξ hξ (U := (V ⊓ W a) ⊓ (V ⊓ W b)) fun h => by
      have h1 := le_preimage_mono ξ inf_le_left h
      have h2 := le_preimage_mono ξ inf_le_right h
      have h3 := le_preimage_mono ξ inf_le_left h1
      exact ((valR_res ξ inf_le_left h _).trans (valR_res ξ _ h1 _)).trans ((hu h3 _ _
        (hf a F ξ (le_preimage_mono ξ inf_le_right h1) h3) (hf b F ξ (le_preimage_mono ξ inf_le_right h2) h3)).trans
        ((valR_res ξ inf_le_right h _).trans (valR_res ξ _ h2 _)).symm))
  refine ⟨s, fun K _ g hg => ?_⟩
  let y : V := ⟨g (IsLocalRing.closedPoint K), hg trivial⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ W y := (le_preimage_iff g _).2 (hy y)
  have h2 := le_inf' hg h1
  have e : valF g V s = valF g (W y) (f y) := (valR_res g inf_le_left h2 s).symm.trans
    ((congrArg (valR g _) (hs y)).trans (valR_res g _ h2 _))
  exact e ▸ hf y K g h1 hg

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ (F : Type) (_ : Field F) (ξ : Sp F ⟶ Y), ∀ w, ξ w = genericPoint Y :=
  ⟨Y.residueField (genericPoint Y), inferInstance, Y.fromSpecResidueField _,
    fun _ => Scheme.fromSpecResidueField_apply _ _⟩

end GlobalTheory.ZH.PowSec
end

