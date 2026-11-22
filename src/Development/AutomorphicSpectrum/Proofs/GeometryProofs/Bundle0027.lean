import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TensDeg

lemma zpow_mem_of_unit {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat n => simpa using pow_mem h n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

lemma exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {s t : Ω} (ht : t ≠ 0)
    (h : Submodule.span R {s} = Submodule.span R {t}) : ∃ u, u ∈ R ∧ u⁻¹ ∈ R ∧ s = u * t := by
  have h1 : s ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span R {s} := h ▸ Submodule.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * t = s := ha
  have hb' : (b : Ω) * s = t := hb
  have hba : (b : Ω) * a = 1 := by
    apply mul_right_cancel₀ ht
    rw [_root_.mul_assoc, ha', hb', _root_.one_mul]
  refine ⟨a, a.2, ?_, ha'.symm⟩
  rw [inv_eq_of_mul_eq_one_left hba]
  exact b.2

lemma zpow_finset_sum {Ω I : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

end GlobalTheory.CompanionTheory.Ar.TensDeg

open GlobalTheory.CompanionTheory.Ar.TensDeg in

theorem GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  intro X Ω _ ξ K _ J y I _ Λ T d e h a
  have he : ∀ i, e i ≠ 0 := fun i => (h i).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩
  intro p hp c hc
  have hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  let g : I → Ω := fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i
  have hg0 : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)
  have hgen : ∀ i, (Λ i).IsGenAt p (g i) := fun i => ⟨hg0 i, (h i).2 p hp c hc⟩
  have hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i := by
    simp only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_apply, zpow_finset_sum (hy k)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  rw [hG]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    choose u hu hu' hsu using fun i =>
      exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)
    have hm : ∏ i, u i ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hsu i, mul_zpow]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundle
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace LatTens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_mem_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s)
    (ht : Λ.IsGenAt p t) : s / t ∈ regAt ξ p := by
  obtain ⟨_, hsΛ⟩ := hs
  obtain ⟨ht0, htΛ⟩ := ht
  have hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω) := by
    rw [← htΛ, hsΛ]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr' : (r : Ω) * t = s := by
    first
    | exact hr
    | simpa [Subring.smul_def] using hr
  rw [← hr', mul_div_assoc, div_self ht0, _root_.mul_one]
  exact r.2

theorem zpow_mem_of_inv_mem {R : Subring Ω} {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (a : ℤ) : u ^ a ∈ R := by
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)

theorem tens_eq_span {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) :
    Lat.tens Λ a p = Submodule.span (regAt ξ p) {∏ i, s i ^ a i} := by
  rw [show Lat.tens Λ a p = Submodule.span (regAt ξ p)
      {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩
    · refine prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)
      rw [inv_div]
      exact div_mem_of_isGenAt (hs i) (hs' i)
    · show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem isGenAt_tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, tens_eq_span Λ a p s hs⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1

theorem mem_finset_inf {I : Type} (S : Finset I) (U : I → X.Opens) (x : X) :
    x ∈ S.inf U ↔ ∀ i ∈ S, x ∈ U i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.inf_empty]
    exact ⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩
  · intro j S' _ ih
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    rw [Finset.forall_mem_insert]

theorem isGenAt_of_isFrameAt {Λ : Lat ξ Ω} {b : Fin 1 → Ω} {p : Cpt ξ} (h : Λ.IsFrameAt b p) :
    Λ.IsGenAt p (b 0) := by
  refine ⟨LinearIndependent.ne_zero 0 h.1, ?_⟩
  rw [h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]

theorem isFrameAt_of_isGenAt {Λ : Lat ξ Ω} {c : Ω} {p : Cpt ξ} (h : Λ.IsGenAt p c) :
    Λ.IsFrameAt (fun _ : Fin 1 => c) p := by
  refine ⟨linearIndependent_unique_iff.mpr h.1, ?_⟩
  rw [h.2, Set.range_const]

theorem tens_isVBOn (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type)
    [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (h : ∀ i, (Λ i).IsVBOn T 1 ⊤) (a : I → ℤ) :
    (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) →
      (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩
  intro p hp
  choose U hpU b _ hfr using fun i => h i p hp
  refine ⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i,
    fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩
  · have hc : (∏ i, b i 0 ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
      zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)
    rw [Set.range_const, eq_top_iff]
    intro y _
    rw [Submodule.mem_span_singleton]
    exact ⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩
  · intro q hq hqU
    rw [mem_finset_inf] at hqU
    exact isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i =>
      isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))

end LatTens

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatPull

theorem isVBOn_pull :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
      (i : Ω →+* Ω') (E' : Type) [AddCommGroup E'] [Module Ω' E'] (j : E →+ E') (L : Lat ξ E) (T : Set (Cpt ξ))
      (r : ℕ) (V : Submodule Ω E), Dominates ξ' ξ f i → (∀ (a : Ω) e, j (a • e) = i a • j e) →
      (∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) →
      L.IsVBOn T r V →
      (L.pull ξ' f j).IsVBOn {p' | ∃ h : genPt ξ ⤳ f p'.1, (⟨f p'.1, h⟩ : Cpt ξ) ∈ T} r
        (Submodule.span Ω' (j '' V)) := by
  intro X Ω _ ξ E _ _ X' Ω' _ ξ' f i E' _ _ j L T r V hd hj hli hvb p' hp'
  obtain ⟨h, hT⟩ := hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hT
  have hind' : LinearIndependent Ω' fun k => j (b k) := hli r b (hfr _ hT hU).1
  have hbV : ∀ k, b k ∈ V := fun k => hb ▸ Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ v ∈ Submodule.span Ω (Set.range b),
      j v ∈ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  refine ⟨f ⁻¹ᵁ U, hU, fun k => j (b k), ?_, ?_⟩
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨b k, hbV k, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      exact key v (by rw [hb]; exact hv)
  · rintro q' ⟨h', hT'⟩ hq'
    refine ⟨hind', ?_⟩
    have hL := (hfr _ hT' hq').2
    obtain ⟨h2, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q'.1, h'⟩) (Set.range b),
        j e ∈ Submodule.span (regAt ξ' q') (Set.range fun k => j (b k)) := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q') • j x := hj a x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨h3, e, he, rfl⟩
      exact key' e (by rw [← hL]; exact he)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨h', b k, ?_, rfl⟩
      rw [hL]
      exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.LatPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) (v : T ⟶ G') :
    Over.mk g ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    have e : (v.left ≫ φ) ≫ G.hom = g := by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hg]
    exact e)

def pull (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (a : Over.mk g ⟶ G) : T ⟶ G' :=
  Over.homMk (h.1.lift a.left T.hom (by rw [hg]; exact Over.w a)) (h.1.lift_snd _ _ _)

def pts (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) :
    (T ⟶ G') ≃* (Over.mk g ⟶ G) where
  toFun := push h hg
  invFun := pull h hg
  left_inv v := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w v).symm
  right_inv a := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  map_mul' v w := by
    subst hg
    exact Over.OverMorphism.ext (h.2 T v w _ _ rfl rfl).symm

theorem pts_left (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (v : T ⟶ G') : (pts h hg v).left = v.left ≫ φ := rfl

variable {R : Type} [CommRing R]

theorem one_left (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (1 : Over.mk x' ⟶ G').left ≫ φ = (1 : Over.mk (x' ≫ f) ⟶ G).left := by
  have e := map_one (pts h (T := Over.mk x') (g := x' ≫ f) rfl)
  exact (pts_left h rfl _).symm.trans (congrArg (fun z => z.left) e)

theorem eps_assoc (x' : Sp R ⟶ S') : (epsAt x').hom ≫ f = (epsAt (x' ≫ f)).hom :=
  Category.assoc _ _ _

abbrev tanPts (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (epsAt x' ⟶ G') ≃* (epsAt (x' ≫ f) ⟶ G) :=
  pts h (T := epsAt x') (g := (epsAt (x' ≫ f)).hom) (eps_assoc x')

theorem fst_comp_base (x' : Sp R ⟶ S') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (epsAt x').hom = x' := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = 𝟙 _ := by
    ext r
    simp
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp, Spec.map_id] at e'
  show _ ≫ Spec.map _ ≫ x' = x'
  rw [← Category.assoc, e', Category.id_comp]

theorem epsMul_comp_base (x' : Sp R ⟶ S') (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (epsAt x').hom = (epsAt x').hom := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ CommRingCat.ofHom (epsMul c) =
      CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show epsMul c (algebraMap R (DualNumber R) r) = algebraMap R (DualNumber R) r
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [epsMul]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show _ ≫ Spec.map _ ≫ x' = Spec.map _ ≫ x'
  rw [← Category.assoc, e']

theorem isTan_iff (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') (v : epsAt x' ⟶ G') :
    IsTanAt G (x' ≫ f) (tanPts h x' v) ↔ IsTanAt G' x' v := by
  unfold IsTanAt
  constructor
  · intro t
    apply h.1.hom_ext
    · rw [Category.assoc, one_left h x', ← pts_left h (eps_assoc x') v]
      exact t
    · rw [Category.assoc, Over.w v, fst_comp_base]
      exact (Over.w (1 : Over.mk x' ⟶ G')).symm
  · intro t
    rw [← one_left h x', ← t, pts_left h (eps_assoc x') v, Category.assoc]

def modelPull (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (x' ≫ f) E) : LieModel G' x' E where
  pt e := (tanPts h x').symm (M.pt e)
  tan e := (isTan_iff h x' _).1 (by rw [MulEquiv.apply_symm_apply]; exact M.tan e)
  inj e e' w := M.inj ((tanPts h x').symm.injective w)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' v).2 t)
    exact ⟨e, by rw [he, MulEquiv.symm_apply_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    apply h.1.hom_ext
    · have a : ∀ e, ((tanPts h x').symm (M.pt e)).left ≫ φ = (M.pt e).left := fun e => by
        rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]
      rw [Category.assoc, a, a]
      exact M.smul c e
    · have b : ((tanPts h x').symm (M.pt e)).left ≫ G'.hom = (epsAt x').hom := Over.w _
      rw [Category.assoc, Over.w, b]
      exact (epsMul_comp_base x' c).symm

def modelPush (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G' x' E) : LieModel G (x' ≫ f) E where
  pt e := tanPts h x' (M.pt e)
  tan e := (isTan_iff h x' _).2 (M.tan e)
  inj e e' w := M.inj ((tanPts h x').injective w)
  onto v t := by
    have t' : IsTanAt G (x' ≫ f) (tanPts h x' ((tanPts h x').symm v)) := by
      rw [MulEquiv.apply_symm_apply]; exact t
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' _).1 t')
    exact ⟨e, by rw [he, MulEquiv.apply_symm_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem lieModel_pullback : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  intro S S' G G' _ _ f φ h R _ x' E _ _
  refine ⟨fun M => ⟨modelPull h x' M, fun e => ?_⟩, fun M' => ⟨modelPush h x' M', fun e => rfl⟩⟩
  show ((tanPts h x').symm (M.pt e)).left ≫ φ = _
  rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RegAtRing

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def stalkEquiv (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ hab => h.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem genMap_germ (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg s) := by
  obtain ⟨q, hq⟩ := p
  have e := congrArg (fun f => (f ≫ Scheme.stalkClosedPointTo ξ).hom s)
    (X.presheaf.germ_stalkSpecializes hp hq)
  simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact e

theorem exists_div (h : IsCptGen ξ) (p : Cpt ξ) (z : Ω) :
    ∃ a b : regAt ξ p, z = (a : Ω) / (b : Ω) := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (show p.1 ∈ (⊤ : X.Opens) from trivial)
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨t, rfl⟩ := h.bij.2 z
  change X.presheaf.stalk (genPt ξ) at t
  let x : U := ⟨genPt ξ, hgU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (x : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf x).asIdeal.primeCompl
    (S := X.presheaf.stalk (x : X)) t
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (x : X)) a s
  simp only at hs
  rw [hs] at hspec
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) :=
    IsLocalization.map_units _ s
  have hne : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) ≠ 0 :=
    (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨genMap ξ p (X.presheaf.germ U p.1 hpU a), ⟨_, rfl⟩⟩,
    ⟨genMap ξ p (X.presheaf.germ U p.1 hpU (s : Γ(X, U))), ⟨_, rfl⟩⟩, ?_⟩
  simp only [genMap_germ p U hpU hgU]
  have hspec' : t * X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U)) = X.presheaf.germ U (genPt ξ) hgU a := hspec
  have hne' : ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) : Ω) ≠ 0 := hne
  have key : (Scheme.stalkClosedPointTo ξ).hom t *
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU a) := by
    rw [← congrArg (Scheme.stalkClosedPointTo ξ).hom hspec']
    exact (map_mul _ _ _).symm
  exact (eq_div_iff hne').2 key

theorem regAt_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  intro X Ω _ ξ h p
  refine ⟨?_, fun _ => isNoetherianRing_of_ringEquiv _ (stalkEquiv h p),
    fun _ => IsIntegrallyClosed.of_equiv (stalkEquiv h p)⟩
  haveI : FaithfulSMul (regAt ξ p) Ω :=
    (faithfulSMul_iff_algebraMap_injective (regAt ξ p) Ω).2 Subtype.val_injective
  exact IsFractionRing.of_field (regAt ξ p) Ω fun z => exists_div h p z

end GlobalTheory.CompanionTheory.Ar.RegAtRing
end
end

