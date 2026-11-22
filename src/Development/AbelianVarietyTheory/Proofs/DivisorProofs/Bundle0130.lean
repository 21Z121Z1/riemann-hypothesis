import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
section
open GlobalTheory

namespace GlobalTheory

open MvPolynomial

variable {R : Type} [CommRing R] {n : ℕ}

theorem eval_mem_span_pow_of_le_degree (z : Fin n → R) (m : ℕ) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ≠ 0 → m ≤ β.degree) :
    MvPolynomial.eval z P ∈ Ideal.span (Set.range z) ^ m := by
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have h1 := monoVal_mem_pow z (⟨β, rfl⟩ : MonoDeg (Fin n) β.degree)
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_le_pow_right (hP β (MvPolynomial.mem_support_iff.mp hβ)) h1)

theorem exists_eval_eq_shift (z : Fin n → R) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ∈ Ideal.span (Set.range z)) :
    ∃ G : MvPolynomial (Fin n) R, MvPolynomial.eval z G = MvPolynomial.eval z P ∧
      ∀ γ, G.coeff γ ≠ 0 → ∃ β j, P.coeff β ≠ 0 ∧ γ = β + Finsupp.single j 1 := by
  classical
  choose g hg using fun β => (Ideal.mem_span_range_iff_exists_fun).mp (hP β)
  refine ⟨∑ β ∈ P.support, ∑ j, MvPolynomial.monomial (β + Finsupp.single j 1) (g β j), ?_, ?_⟩
  · have key : ∀ β j, MvPolynomial.eval z (MvPolynomial.monomial (β + Finsupp.single j 1) (g β j))
        = g β j * z j * monoVal z β := by
      intro β j
      rw [MvPolynomial.eval_monomial]
      change _ * monoVal z _ = _
      rw [monoVal_add, monoVal_single, pow_one]
      ring
    simp only [map_sum, key]
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_mul, hg β]
    rfl
  · intro γ hγ
    rw [MvPolynomial.coeff_sum] at hγ
    obtain ⟨β, hβ, hβ'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
    rw [MvPolynomial.coeff_sum] at hβ'
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ'
    rw [MvPolynomial.coeff_monomial] at hj
    split_ifs at hj with h
    · exact ⟨β, j, MvPolynomial.mem_support_iff.mp hβ, h.symm⟩
    · exact absurd rfl hj

theorem weightedRelation_step (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D k : ℕ) (H : MvPolynomial (Fin n) R)
    (hH : ∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β)
    (h0 : MvPolynomial.eval z H = 0) :
    (∀ β : Fin n →₀ ℕ, β.degree = k → H.coeff β ∈ Ideal.span (Set.range z)) ∧
      ∃ H' : MvPolynomial (Fin n) R,
        (∀ β, H'.coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β) ∧
        MvPolynomial.eval z H' = 0 ∧
        ∀ β : Fin n →₀ ℕ, Finsupp.weight w β = D → k + 1 ≤ β.degree → H'.coeff β = H.coeff β := by
  classical
  set Hk := MvPolynomial.homogeneousComponent k H with hHk
  have hcoeffk : ∀ β, Hk.coeff β = if β.degree = k then H.coeff β else 0 := fun β =>
    MvPolynomial.coeff_homogeneousComponent _ _ _
  have hrest : ∀ β, (H - Hk).coeff β = if β.degree = k then 0 else H.coeff β := by
    intro β
    rw [MvPolynomial.coeff_sub, hcoeffk]
    split_ifs <;> simp
  have hrest' : ∀ β, (H - Hk).coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β := by
    intro β hβ
    rw [hrest] at hβ
    split_ifs at hβ with h
    · exact absurd rfl hβ
    · have := hH β hβ
      exact ⟨by omega, this.2⟩
  have hmem : MvPolynomial.eval z Hk ∈ Ideal.span (Set.range z) ^ (k + 1) := by
    have h1 := eval_mem_span_pow_of_le_degree z (k + 1) (H - Hk) fun β hβ => (hrest' β hβ).1
    have h2 : MvPolynomial.eval z Hk = - MvPolynomial.eval z (H - Hk) := by
      rw [map_sub, h0]
      ring
    rw [h2]
    exact neg_mem h1
  have hI : ∀ β, Hk.coeff β ∈ Ideal.span (Set.range z) :=
    (isQuasiRegularSeq_self_iff z).mp hz k Hk
      (MvPolynomial.homogeneousComponent_isHomogeneous k H) hmem
  refine ⟨fun β hβ => ?_, ?_⟩
  · have := hI β
    rwa [hcoeffk, if_pos hβ] at this
  obtain ⟨G, hG, hGs⟩ := exists_eval_eq_shift z Hk hI
  have hGw : ∀ γ, G.coeff γ ≠ 0 → k + 1 ≤ γ.degree ∧ D + 1 ≤ Finsupp.weight w γ := by
    intro γ hγ
    obtain ⟨β, j, hβ, rfl⟩ := hGs γ hγ
    rw [hcoeffk] at hβ
    split_ifs at hβ with hd
    · have := hH β hβ
      have hj := hw j
      simp only [map_add, Finsupp.degree_single, Finsupp.weight_single, one_smul, hd]
      exact ⟨le_rfl, by omega⟩
    · exact absurd rfl hβ
  refine ⟨(H - Hk) + G, ?_, ?_, ?_⟩
  · intro β hβ
    rw [MvPolynomial.coeff_add] at hβ
    by_cases h1 : (H - Hk).coeff β = 0
    · rw [h1, zero_add] at hβ
      have := hGw β hβ
      exact ⟨this.1, by omega⟩
    · exact hrest' β h1
  · rw [map_add, hG, ← map_add, sub_add_cancel, h0]
  · intro β hβw hβd
    rw [MvPolynomial.coeff_add, hrest, if_neg (by omega)]
    by_cases h : G.coeff β = 0
    · rw [h, add_zero]
    · have := hGw β h
      omega

theorem weightedRelation_coeff_mem (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D : ℕ) (j : ℕ) : ∀ (k : ℕ) (H : MvPolynomial (Fin n) R),
    (∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β) →
    MvPolynomial.eval z H = 0 → ∀ α : Fin n →₀ ℕ, α.degree = k + j →
    Finsupp.weight w α = D → H.coeff α ∈ Ideal.span (Set.range z) := by
  induction j with
  | zero =>
    intro k H hH h0 α hα _
    exact (weightedRelation_step z w hw hz D k H hH h0).1 α hα
  | succ j ih =>
    intro k H hH h0 α hα hαw
    obtain ⟨-, H', h1, h2, h3⟩ := weightedRelation_step z w hw hz D k H hH h0
    rw [← h3 α hαw (by omega)]
    exact ih (k + 1) H' h1 h2 α (by omega) hαw

theorem coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero {R : Type} [CommRing R] {n : ℕ}
    (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) (hz : IsQuasiRegularSeq R z) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsWeightedHomogeneous w D)
    (h0 : MvPolynomial.eval z F = 0) (α : Fin n →₀ ℕ) :
    F.coeff α ∈ Ideal.span (Set.range z) := by
  by_cases hα : F.coeff α = 0
  · rw [hα]
    exact zero_mem _
  exact weightedRelation_coeff_mem z w hw hz D α.degree 0 F
    (fun β hβ => ⟨Nat.zero_le _, (hF hβ).ge⟩) h0 α (zero_add _).symm (hF hα)

theorem weightedRelation_coeff_mem_span : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R)
    (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) :=
  fun z w hw hz D F hF h0 α =>
    coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero z w hw hz D F hF h0 α

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherent
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    letI := (ρ.restrict S S' hρ).toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : S) S' := by
  letI := ρ.toAlgebra
  letI := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := isLocalizationAway F α hα U.2 f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

def IsFinFlatRk {X Y : Scheme.{0}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = r

lemma IsFinFlatRk.of_isPullback {P X Y T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ Y}
    {g : T ⟶ Y} (h : IsPullback fst snd f g) {r : ℕ} (hf : IsFinFlatRk f r) : IsFinFlatRk snd r := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h h1,
    MorphismProperty.of_isPullback (P := @Flat) h h2, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g h y, h3]

lemma IsFinFlatRk.iso_comp {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y} {r : ℕ}
    (hf : IsFinFlatRk f r) : IsFinFlatRk (e ≫ f) r :=
  IsFinFlatRk.of_isPullback (IsPullback.of_horiz_isIso (fst := e) (g := 𝟙 Y) ⟨by simp⟩) hf

lemma isPullback_comap {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f))
      f I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

variable {S Z : Scheme.{0}} (z : Z ⟶ S)

def bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    pullback z k ⟶ pullback z g :=
  pullback.map z k z g (𝟙 Z) c (𝟙 S) (by simp) (by rw [Category.comp_id, w])

lemma isPullback_bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    IsPullback (bc z c g k w) (pullback.snd z k) (pullback.snd z g) c := by
  subst w
  refine IsPullback.of_right ?_ (by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]) (IsPullback.of_hasPullback z g)
  have e : bc z c g (c ≫ g) rfl ≫ pullback.fst z g = pullback.fst z (c ≫ g) := by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]
  rw [e]
  exact IsPullback.of_hasPullback z (c ≫ g)

lemma bc_id {T : Scheme.{0}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) : bc z (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [bc]

lemma bc_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (m : R ⟶ S)
    (w : a ≫ g = k) (w' : b ≫ k = m) (w'' : (b ≫ a) ≫ g = m) :
    bc z (b ≫ a) g m w'' = bc z b k m w' ≫ bc z a g k w := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

variable (r : ℕ)

abbrev HIdeal {T : Scheme.{0}} (g : T ⟶ S) : Type :=
  {I : (pullback z g).IdealSheafData // IsFinFlatRk (I.subschemeι ≫ pullback.snd z g) r}

abbrev HPt (T : Scheme.{0}) : Type := Σ g : T ⟶ S, HIdeal z r g

variable {z r}

def HIdeal.pull {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HIdeal z r k :=
  ⟨I.1.comap (bc z c g k w), IsFinFlatRk.of_isPullback
    ((isPullback_comap I.1 (bc z c g k w)).flip.paste_vert (isPullback_bc z c g k w)) I.2⟩

def HPt.map {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) : HPt z r T' :=
  ⟨c ≫ x.1, x.2.pull c rfl⟩

lemma HPt.map_mk {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HPt.map c ⟨g, I⟩ = ⟨k, I.pull c w⟩ := by
  subst w; rfl

lemma HPt.mk_eq_mk_iff {T : Scheme.{0}} {g : T ⟶ S} (I J : HIdeal z r g) :
    (⟨g, I⟩ : HPt z r T) = ⟨g, J⟩ ↔ I.1 = J.1 := by
  rw [Sigma.mk.inj_iff, heq_iff_eq, Subtype.ext_iff]
  simp

lemma HPt.map_eq_mk_iff {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) {k : T' ⟶ S}
    (w : c ≫ x.1 = k) (J : HIdeal z r k) :
    HPt.map c x = ⟨k, J⟩ ↔ x.2.1.comap (bc z c x.1 k w) = J.1 := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk c w, HPt.mk_eq_mk_iff]
  rfl

lemma HPt.map_id {T : Scheme.{0}} (x : HPt z r T) : HPt.map (𝟙 T) x = x := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (𝟙 T) (Category.id_comp g), HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (𝟙 T) g g _) = I.1
  rw [bc_id, Scheme.IdealSheafData.comap_id]

lemma HPt.map_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (x : HPt z r T) :
    HPt.map (b ≫ a) x = HPt.map b (HPt.map a x) := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (b ≫ a) (Category.assoc b a g), HPt.map_mk a rfl, HPt.map_mk b rfl, HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (b ≫ a) g _ _) = (I.1.comap (bc z a g _ rfl)).comap (bc z b (a ≫ g) _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, bc_comp z b a g (a ≫ g) (b ≫ a ≫ g) rfl rfl]

variable (z r)

def hilbFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := HPt z r T.unop
  map c := TypeCat.ofHom (HPt.map c.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x => HPt.map_id x
  map_comp a b := ConcreteCategory.hom_ext _ _ fun x => HPt.map_comp _ _ x

def hilbProj : hilbFunctor z r ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun x => x.1

variable {z r}

lemma IsFinFlatRk.ker_subschemeι {T V : Scheme.{0}} {g : T ⟶ S} (v : V ⟶ pullback z g)
    [IsClosedImmersion v] (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) :
    IsFinFlatRk (v.ker.subschemeι ≫ pullback.snd z g) r := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc]
  exact hv.iso_comp _

def mkPt {T V : Scheme.{0}} (g : T ⟶ S) (v : V ⟶ pullback z g) [IsClosedImmersion v]
    (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) : HPt z r T :=
  ⟨g, v.ker, hv.ker_subschemeι v⟩

theorem comap_eq_ker_iff {X Y V : Scheme.{0}} (m : X ⟶ Y) (I : Y.IdealSheafData) (v : V ⟶ X)
    [IsClosedImmersion v] : I.comap m = v.ker ↔ ∃ w : V ⟶ I.subscheme, IsPullback v w m I.subschemeι := by
  constructor
  · intro h
    have H : I.subschemeι.ker ≤ (v ≫ m).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift I.subschemeι (v ≫ m) H,
      isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_⟩
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  · rintro ⟨w, hP⟩
    rw [← hP.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end GlobalTheory.HilbGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpolyStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_of_commute_of_charpoly_separable' : ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable → a * y = y * a → b * y = y * b → a * b = b * a := by
  first | exact @GlobalTheory.commute_of_commute_separable_charpoly | exact GlobalTheory.commute_of_commute_separable_charpoly | (intros; apply GlobalTheory.commute_of_commute_separable_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
section
namespace GlobalTheory

theorem commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  classical
  have expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U),
      rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) •
        rd ((Module.finBasis K U j : U) : A) := by
    intro U _ f
    conv_lhs => rw [← (Module.finBasis K U).sum_repr f]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]
  set bV := Module.finBasis K V with hbV
  set bV' := Module.finBasis K V' with hbV'
  let gV : Fin (Module.finrank K V) → R := fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩
  let gV' : Fin (Module.finrank K V') → R := fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩
  have liV : LinearIndependent ℂ gV := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind _ (fun j => (bV j : A)) (fun j => (bV j).2)
      (bV.linearIndependent.map' V.subtype V.ker_subtype)
  have liV' : LinearIndependent ℂ gV' := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2)
      (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)
  let W := Submodule.span ℂ (Set.range gV)
  let W' := Submodule.span ℂ (Set.range gV')
  have eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV]
    exact expand V f
  have eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV']
    exact expand V' f
  have memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W := by
    intro f
    rw [eqV f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W' := by
    intro f
    rw [eqV' f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Module.Basis (Fin (Module.finrank K V)) ℂ W := Module.Basis.span liV
  have bW_apply : ∀ j, (bW j : R) = gV j := fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)
  let img : Fin (Module.finrank K V) → W' := fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩
  let Tc : W →ₗ[ℂ] W' := bW.constr ℂ img
  have Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩ := by
    intro f
    have e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]
      exact eqV f
    rw [e1, map_sum]
    simp only [map_smul, Tc, Module.Basis.constr_basis]
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finset_sum,
      SetLike.val_smul, img]
    conv_rhs => rw [← bV.sum_repr f]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]
  have Tc_basis : ∀ i, Tc (bW i) = img i := fun i => by
    simp only [Tc, Module.Basis.constr_basis]
  haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW
  have Tc_ne : Tc ≠ 0 := by
    obtain ⟨f, hf⟩ : ∃ f, T f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hT (LinearMap.ext hc)
    have hfA : (T f : A) ≠ 0 := fun hz => hf (Subtype.ext hz)
    have li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A)) :=
      hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2)
        (linearIndependent_unique_iff.mpr hfA)
    have hne : rd (T f : A) ≠ 0 := li1.ne_zero 0
    intro h0
    apply hne
    have := congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)
    simp only [h0, LinearMap.zero_apply] at this
    simpa using this.symm
  have spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩
  have hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W := by
    intro w hw
    have hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (⟨h', hh'⟩ : R) * gV' i ∈ W
      obtain ⟨z, hz, hzeq⟩ := spanLe (hsub _ (bV' i).2)
      have : z = (⟨h', hh'⟩ : R) * gV' i := Subtype.ext hzeq
      rw [← this]; exact hz
    exact hle hw
  have hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R) := by
    let B1 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype
    let B2 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)
    have hB : B1 = B2 := by
      refine bW.ext fun i => bW.ext fun j => ?_
      simp only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mul_apply', Tc_basis, bW_apply]
      apply Subtype.ext
      simp only [img, gV, Subalgebra.coe_mul, ← map_mul]
      rw [hcomm]
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa [B1, B2] using this
  have hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1 := Subtype.ext (by simpa using hhh)
  obtain ⟨a, ha, hkey⟩ := commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc
  refine ⟨a, ha, fun f => ?_⟩
  have := congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)
  rw [Tc_rd] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s)) (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s → ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  first | exact @GlobalTheory.component_in_fibre_iff_of_isPullback | exact GlobalTheory.component_in_fibre_iff_of_isPullback | (intros; apply GlobalTheory.component_in_fibre_iff_of_isPullback <;> assumption)
end

