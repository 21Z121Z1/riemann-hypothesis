import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSetPull

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d) : Set.range a = c ⁻¹' Set.range d := by
  rw [← AlgebraicGeometry.Scheme.Pullback.range_fst c d]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.hom q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  refine ⟨{ toFun := fun x => Over.homMk (x.left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl)
            invFun := fun y => Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
            left_inv := fun x => by
              apply Over.OverMorphism.ext
              apply h.1.hom_ext
              · exact h.1.lift_fst _ _ _
              · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
            right_inv := fun y => by
              apply Over.OverMorphism.ext
              exact h.1.lift_fst _ _ _
            map_mul' := fun x y => by
              apply Over.OverMorphism.ext
              exact (h.2 T x y _ _ rfl rfl).symm }, fun x => rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
  {t' : SAB H S'} {f : S' ⟶ S}

theorem heckeKer_iff (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (T : Over S')
    (C' : Subgroup (T ⟶ t'.G)) (C : Subgroup (Over.mk (T.hom ≫ f) ⟶ t.G))
    (h : ∀ (u : T ⟶ t'.G) (v : Over.mk (T.hom ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) :
    t'.HeckeKer T D P p i C' ↔ t.HeckeKer (Over.mk (T.hom ≫ f)) D P p i C := by
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart T
  have hC : ∀ u, u ∈ C' ↔ ρ u ∈ C := fun u => h u (ρ u) (hρ u)
  have hact : ∀ u a, ρ (u ≫ t'.act.act a) = ρ u ≫ t.act.act a := by
    intro u a
    apply Over.OverMorphism.ext
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) (m.act a)
  have htors : ∀ I u, u ∈ t'.tors T I ↔ ρ u ∈ t.tors (Over.mk (T.hom ≫ f)) I := by
    intro I u
    simp only [SAB.tors, Set.mem_ofPred_eq]
    refine forall₂_congr fun a _ => ?_
    rw [← hact, map_eq_one_iff ρ ρ.injective]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hW : ∀ u v, Out.WeilIs t'.G t'.PP.L ((p : ℤ) ^ 2) u v 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) (ρ u) (ρ v) 1 :=
    fun u v => GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      T _ u v (ρ u) (ρ v) 1 (hρ u) (hρ v)
  have cC : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv hC)
  have cT : ∀ I, Nat.card (t'.tors T I) = Nat.card (t.tors (Over.mk (T.hom ≫ f)) I) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv (htors I))
  have cI : ∀ I, Nat.card ((C' : Set (T ⟶ t'.G)) ∩ t'.tors T I : Set (T ⟶ t'.G)) =
      Nat.card ((C : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) ∩ t.tors (Over.mk (T.hom ≫ f)) I : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv fun u => (hC u).and (htors I u))
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx a
      obtain ⟨u, rfl⟩ := ρ.surjective x
      rw [← hact]
      exact (hC _).mp (h1 u ((hC u).mpr hx) a)
    · intro J hJ x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (hC u).mp (h2 J hJ ((htors J u).mpr hx))
    · intro x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (htors _ u).mp (h3 ((hC u).mpr hx))
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := ρ.surjective x
      obtain ⟨v, rfl⟩ := ρ.surjective y
      exact (hW u v).mp (h4 u ((hC u).mpr hx) v ((hC v).mpr hy))
    · rw [← cC]
      exact h5
    · rw [← cT, ← cI]
      exact h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu a
      rw [hC, hact]
      exact h1 _ ((hC u).mp hu) a
    · intro J hJ u hu
      exact (hC u).mpr (h2 J hJ ((htors J u).mp hu))
    · intro u hu
      exact (htors _ u).mpr (h3 ((hC u).mp hu))
    · intro u hu v hv
      exact (hW u v).mpr (h4 _ ((hC u).mp hu) _ ((hC v).mp hv))
    · rw [cC]
      exact h5
    · rw [cT, cI]
      exact h6

theorem heckeSet_pull (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (K : Set t.G.left)
    (hK : HeckeSet D t P p i K) : HeckeSet D t' P p i (m.φ ⁻¹' K) := by
  intro k _ _ x
  obtain ⟨C, hCK, hC⟩ := hK k (x ≫ f)
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart (Over.mk x)
  refine ⟨C.comap ρ.toMonoidHom, fun z => ?_, ?_⟩
  · show ρ z ∈ C ↔ _
    rw [hCK, hρ]
    simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]
    exact Iff.rfl
  · refine (heckeKer_iff D P p i m (Over.mk x) _ C ?_).mpr hC
    intro u v huv
    obtain rfl : v = ρ u := Over.OverMorphism.ext (huv.trans (hρ u).symm)
    exact Iff.rfl

theorem etSet_pull {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    (K : Set G.left) (hK : EtSet G K) : EtSet G' (φ ⁻¹' K) := by
  obtain ⟨C, j, hfin, het, hcl, hCK⟩ := hK
  have w : (pullback.fst C.hom f ≫ j.left) ≫ G.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, Over.w j, pullback.condition]
  let j' : Over.mk (pullback.snd C.hom f) ⟶ G' :=
    Over.homMk (h.lift (pullback.fst C.hom f ≫ j.left) (pullback.snd C.hom f) w) (h.lift_snd _ _ _)
  have sq : IsPullback (pullback.fst C.hom f) j'.left j.left φ := by
    refine IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (h.lift_fst _ _ _).symm h
    have e : j'.left ≫ G'.hom = pullback.snd C.hom f := h.lift_snd _ _ _
    rw [e, Over.w j]
    exact IsPullback.of_hasPullback C.hom f
  refine ⟨Over.mk (pullback.snd C.hom f), j', ?_, ?_, ?_, ?_⟩
  · show IsFinite (pullback.snd C.hom f)
    infer_instance
  · show Etale (pullback.snd C.hom f)
    infer_instance
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hcl
  · rw [range_of_isPullback sq.flip, hCK]

theorem lists_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (K : Set G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (hK : Lists N σ K) :
    ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ G'), (∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left) ∧ Lists N σ' (φ ⁻¹' K) := by
  obtain ⟨ρ, hρ⟩ := exists_equiv h (𝟙_ (Over S'))
  let σ' : Fin n → (𝟙_ (Over S') ⟶ G') := fun j => ρ.symm (toUnit _ ≫ σ j)
  have key : ∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left := by
    intro j
    rw [← hρ, MulEquiv.apply_symm_apply, Over.comp_left, Over.toUnit_left]
    simp [Over.tensorUnit_hom]
  have sq : ∀ j, IsPullback (σ' j).left f φ (σ j).left := by
    intro j
    refine (IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (key j).symm h.1).flip
    rw [Over.w (σ' j), Over.w (σ j)]
    simp only [Over.tensorUnit_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  refine ⟨σ', key, ?_, ?_, ?_⟩
  · intro j
    apply ρ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hK.1 j, MonObj.comp_one, map_one]
  · rw [hK.2.1, Set.preimage_iUnion]
    exact Set.iUnion_congr fun j => (range_of_isPullback (sq j)).symm
  · intro k _ _ x i j hij
    apply hK.2.2 k (x ≫ f)
    have e := congrArg (· ≫ φ) hij
    simp only [Category.assoc, key] at e
    simpa only [Category.assoc] using e

end GlobalTheory.HkSetPull

theorem GlobalTheory.heckeSets_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), IsProper t.G.hom → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (C' : Subgroup (Over.mk x ⟶ t'.G)) (C : Subgroup (Over.mk (x ≫ f) ⟶ t.G)), (∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) → (t'.HeckeKer (Over.mk x) D 𝔓 p i C' ↔ t.HeckeKer (Over.mk (x ≫ f)) D 𝔓 p i C)) ∧ ∀ K : Set t.G.left, (HeckeSet D t 𝔓 p i K → HeckeSet D t' 𝔓 p i (m.φ ⁻¹' K)) ∧ (EtSet t.G K → EtSet t'.G (m.φ ⁻¹' K)) ∧ ∀ (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)), Lists N σ K → ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ t'.G), (∀ j, (σ' j).left ≫ m.φ = f ≫ (σ j).left) ∧ Lists N σ' (m.φ ⁻¹' K) := by
  intro E _ _ _ H D 𝔓 p i S S' t t' f m _
  exact ⟨fun k _ _ x C' C h => GlobalTheory.HkSetPull.heckeKer_iff D 𝔓 p i m (Over.mk x) C' C h,
    fun K => ⟨fun hK => GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m K hK,
      fun hK => GlobalTheory.HkSetPull.etSet_pull m.cart.1 K hK,
      fun N n σ hK => GlobalTheory.HkSetPull.lists_pull m.cart K N n σ hK⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordOfRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out

theorem secCoord_of_ratio {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM' : M'.IsLB) {σ : Type} {th : σ → M.Sec}
    {th' : σ → M'.Sec} {B : Type} [Field B] {x : Sp B ⟶ X} {x' : Sp B ⟶ X'} (p : Sp B) {j : M.ι} {j' : M'.ι}
    (hj : x p ∈ M.U j) (hj' : x' p ∈ M'.U j') (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, gs x' p _ ((th' i).f j') = c * gs x p _ ((th i).f j)) {v : σ → B} (H : SecCoord M th x v) :
    SecCoord M' th' x' v := by
  have hs : ∀ y : Sp B, y = p := fun y => Subsingleton.elim (α := PrimeSpectrum B) _ _
  obtain ⟨u, hu⟩ := loc_of_secCoord H p j hj
  by_cases hv : Ideal.span (Set.range v) = ⊤
  · refine secCoord_of_loc hv fun y l hl => ?_
    obtain rfl := hs y
    refine ⟨gm x' y _ (M'.g l j') * (c * u), fun i => ?_⟩
    rw [gs_sec (th' i) x' y hl hj', h, hu, Units.val_mul, Units.val_mul]
    ring
  · have h0 : ∀ i, v i = 0 := fun i => by
      by_contra hi
      exact hv (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (IsUnit.mk0 _ hi))
    obtain ⟨w, hw⟩ := exists_secCoord (th := th') hM' (x := x') (k := j') fun y => by rw [hs y]; exact hj'
    obtain ⟨u', hu'⟩ := loc_of_secCoord hw p j' hj'
    have : w = v := funext fun i => ev_ext fun y => by
      obtain rfl := hs y
      have := hu' i
      rw [h, hu, h0, map_zero, zero_mul, mul_zero] at this
      rw [h0, map_zero]
      exact (Units.mul_left_eq_zero _).1 this.symm
    exact this ▸ hw

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem secCoord_of_sv {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {L : LB A.left} {L' : LB A'.left}
    (hL' : L'.IsLB) {a a' : ℤ} {T : Over S} {T' : Over S'} {σ : Type} {th : σ → LB.Sec (LPow A L a T)}
    {th' : σ → LB.Sec (LPow A' L' a' T')} {B : Type} [Field B] {x : Sp B ⟶ (T ⊗ A).left}
    {x' : Sp B ⟶ (T' ⊗ A').left} (p : Sp B) {I I'} (hI : Good L p I) (hI' : Good L' p I')
    (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, VVRank.sv A' (th' i) x' p I' = c * VVRank.sv A (th i) x p I) {v : σ → B}
    (H : SecCoord _ th x v) : SecCoord _ th' x' v :=
  secCoord_of_ratio (LB.isLB_linComb hL' _ _) p (hI.mem (fun _ : Fin 1 => (snd T A).left) x)
    (hI'.mem (fun _ : Fin 1 => (snd T' A').left) x') c h H

theorem lab_pow (t : TObj g (N' ^ 2) J b s) (a : Ix g (N' ^ 2)) : t.lab a ^ (N' ^ 2) = 1 := by
  have := t.ab.comm
  have cm : ∀ x y : Out.baseOver S ⟶ t.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ (N' ^ 2) = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, t.torsion, one_pow]

theorem MapBy.lab {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) (a : Ix g (N' ^ 2)) : f ≫ (t.lab a).left = (u.lab a).left ≫ φ := by
  have hτ : f ≫ (baseOver S).hom = (baseOver S').hom ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  refine (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).2 ?_
  simp only [TObj.lab, linComb, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_pow]
  congr 1
  exact (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).1 (h.2.2.1 i).symm

theorem emb_move {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) {m : ℕ} (hm : m ∣ N') {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ]
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {σ₀} (H : t.Emb m T₀ σ₀) : ∃ σ, u.Emb m T σ ∧
      ∀ (B : Type) [Field B] (y : Sp B ⟶ (T ⊗ u.A).left) (y₀ : Sp B ⟶ (T₀ ⊗ t.A).left),
        y₀ ≫ (fst T₀ t.A).left = y ≫ (fst T u.A).left ≫ τ → y₀ ≫ (snd T₀ t.A).left = y ≫ (snd T u.A).left ≫ φ →
        ∀ w, SecCoord _ σ y w ↔ SecCoord _ σ₀ y₀ w := by
  obtain ⟨w, hw⟩ := h.2.1
  have hp := h.1
  have hL₀ := t.isLB
  have hL₁ := u.isLB
  have := u.ab.comm
  obtain ⟨th₀, s₀, α₀, U₀, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th, hth⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s₁, hs⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose σ hσ using fun i => ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ (σ₀ i)
  obtain ⟨α, hα, vα⟩ := ThetaPtMove.exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) α₀ h₂
  have hx : ∀ a, τ ≫ ((Over.homMk T₀.hom (by simp) : T₀ ⟶ Out.baseOver S) ≫ t.lab a).left =
      ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a).left ≫ φ := fun a => by
    show τ ≫ T₀.hom ≫ _ = (T.hom ≫ _) ≫ φ
    rw [← Category.assoc, hτ, Category.assoc, h.lab, Category.assoc]
  have hk : ∀ a, (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 :=
    fun a => by
      rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  choose U hU hU' using fun i =>
    ThetaPtMove.symLift_move hp τ hτ hw hL₀ hL₁ (ThetaPtMove.over_pow hp τ hτ (hx i) _) (hk i) (h₅ i)
  have hg : IsGenSec t.A t.L 1 (VVRank.pullS t.A 1 (𝟙 T₀) th₀) :=
    ThetaCoord.isGenSec_pullS hL₀ _ (𝟙 T₀) (Category.comp_id _) h₁
  refine ⟨σ, ⟨th, s₁, α, U, ThetaPtMove.isGenSec_move hp τ hτ hw hL₀ hL₁ τ (𝟙 T₀) (Category.comp_id _) hth hg, hα,
    ThetaPtMove.isTwistPull_move hp τ hτ hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (hσ i) (h₆ i)⟩, fun B _ y y₀ e₁ e₂ v => ?_⟩
  obtain rfl : y₀ = y ≫ ThetaPtMove.psi hp τ hτ := ThetaPtMove.psi_ext
    (by rw [e₁, Category.assoc, ThetaPtMove.psi_fst']) (by rw [e₂, Category.assoc, ThetaPtMove.psi_snd'])
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL₀ p
  obtain ⟨I', hI'⟩ := ConstFam.exists_good' hL₁ p
  exact ⟨secCoord_of_sv hL₀ p hI' hI _ fun i => hσ i _ y p I I' hI hI',
    secCoord_of_sv hL₁ p hI hI' _ fun i => (Units.eq_inv_mul_iff_mul_eq _).2 (hσ i _ y p I I' hI hI').symm⟩

theorem emb_unique (hG : GlobalFnsSt) (t : TObj g (N' ^ 2) J b s) {m : ℕ} (hm : Odd m) {T : Over S}
    [Subsingleton T.left] {σ σ'} (H : t.Emb m T σ) (H' : t.Emb m T σ') {B : Type} [Field B]
    (y : Sp B ⟶ (T ⊗ t.A).left) {w} (h : SecCoord _ σ y w) : SecCoord _ σ' y w := by
  obtain ⟨th, s₁, α, U, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th', s₁', α', U', h₁', h₂', h₄', h₅', h₆'⟩ := H'
  have hL := t.isLB
  obtain ⟨c, hc⟩ := ThetaCoord.exists_unit_of_isGenSec h₁' h₁
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL p
  refine secCoord_of_sv hL p hI hI
    (val α' y p I * (val α y p I)⁻¹ * gm (y ≫ (fst T t.A).left) p ⊤ c) (fun a => ?_) h
  have e₀ : (U' a).pt = (U a).pt := (h₅' a).pt_eq.trans (h₅ a).pt_eq.symm
  have e₁ := val_corr hI (SymLiftOdd.symLift_unique hG t.ab hL hm.pow _ _ (h₅' a) (h₅ a)) y
  have f₁ : (y ≫ (translT t.A (U a).pt).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
  have f₂ : ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, mulT, lift_fst, f₁]
  have e₂ := CommPairing.val_div_eq hL (fst T t.A).left (CommPairing.surj_fst hG t.ab T) h₂' h₂ _ _ f₁ p I hI
  have e₃ := ThetaAct.sv_smul (c : Γ(T.left, ⊤)) (SecM.ofSec t.A th)
    ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) p hI
  rw [← hc, f₂, gs_unit _ _ ⊤ trivial] at e₃
  rw [VVRank.sv_of_isTwistPull t.A (h₆ a) y p hI, VVRank.sv_of_isTwistPull t.A (h₆' a) y p hI,
    VVRank.sv_of_isTwistPull t.A h₄ _ p hI, VVRank.sv_of_isTwistPull t.A h₄' _ p hI, ← e₂]
  erw [e₁]
  rw [e₀]
  rw [show VVRank.sv t.A th' _ p I = _ * VVRank.sv t.A th _ p I from e₃]
  simp only [Units.val_mul]
  have key : ∀ {Q : Type} [CommRing Q] (a a' : Qˣ) (x y z : Q), x * (a' * (y * z)) = a' * ↑a⁻¹ * y * (x * (a * z)) :=
    fun a a' x y z => by linear_combination (-(x * a' * y * z)) * a.inv_mul
  exact key _ _ _ _ _

end GlobalTheory.TUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

open Topology Filter

theorem t2Space_ptsOver_of_isSeparated {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (s : Sp ℂ ⟶ S) :
    T2Space (Points.PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := Points.PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have hc := (h.isClosedEmbedding.comp
    (Points.PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  convert hc using 1
  have key : ∀ x, h (Points.PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h])) (Subtype.ext (by simp [h]))
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain rfl : a = b := hab
    exact ⟨a, key a⟩
  · rintro ⟨x, hx⟩
    rw [Function.comp_apply, key] at hx
    rw [← hx]
    rfl

theorem exists_realLinear_lift {V W Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Group Q] [TopologicalSpace T] [T2Space T] (j : Q → T)
    (hj : Function.Injective j) (e : W → Q) (e₀ : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (he₀ : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e) (Λ : Submodule ℤ W) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hc : Continuous (j ∘ e)) (hc₀ : Continuous (j ∘ e₀)) :
    ∃ L : V →L[ℝ] W, ∀ z, e (L z) = e₀ z := by
  have heq : ∀ z w, e z = e w ↔ z - w ∈ Λ := fun z w => by
    rw [← hk, ← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]
  have : CompactSpace (W ⧸ Λ) := by
    refine ⟨?_⟩
    rw [← (Submodule.mkQ_surjective Λ).range_eq]
    refine IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => ?_
    rw [map_add, Submodule.mkQ_apply _ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]
  let ē : W ⧸ Λ → T := Quotient.lift (j ∘ e) fun a b hab =>
    congrArg j ((heq a b).2 ((Submodule.quotientRel_def Λ).1 hab))
  have hē : ∀ w, ē (Λ.mkQ w) = j (e w) := fun _ => rfl
  have hemb : IsClosedEmbedding ē := by
    refine (hc.quotient_lift _).isClosedEmbedding fun a b hab => ?_
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Λ.mkQ_surjective b
    exact (Submodule.Quotient.eq Λ).2 ((heq a b).1 (hj hab))
  choose σ hσ using hs
  let φ : V →+ W ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (σ (e₀ z))) fun a b => by
    rw [← map_add]
    exact (Submodule.Quotient.eq Λ).2 ((heq _ _).1 (by rw [he, hσ, hσ, hσ, he₀]))
  have hφ : Continuous φ := hemb.isEmbedding.continuous_iff.2 (hc₀.congr fun z => by
    show j (e₀ z) = j (e (σ (e₀ z)))
    rw [hσ])
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift (ex := φ) (isDiscrete_ker_mkQ Λ)
    (Λ.isOpenMap_mkQ.nhds_le 0) hφ.continuousAt
  exact ⟨L, fun z => ((heq _ _).2 ((Submodule.Quotient.eq Λ).1 (hL z))).trans (hσ _)⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

def IsExp {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

theorem continuous_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) : Continuous a :=
  Points.continuous_of_differentiableOn fun U f => by simpa using h U f

theorem differentiableAt_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) (U : X.Opens) (f : Γ(X, U)) {z : V} (hz : ⊤ ≤ a z ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (a b) U f) z :=
  (h U f).2.differentiableAt ((h U f).1.mem_nhds ⟨trivial, hz⟩)

theorem IsExp.eq_of_fderiv {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e) {w w' : Fin g → ℂ}
    (h : ∀ (U : G.left.Opens) (f : Γ(G.left, U)), ⊤ ≤ (e 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e z).left U f) 0 w') : w = w' := by
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  refine (he.2.2.2.2 v hv.1).unique hv ⟨hv.1, fun U hU f => (hv.2 U hU f).trans (h U f ?_)⟩
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := hv.1
  rw [← h1]
  exact Points.le_preimage_comp _ _ hU (Points.le_preimage_top _)

theorem map_zero_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem eq_iff_sub_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  rw [← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]

theorem IsExp.exists_linearEquiv [IsSeparated G.hom] {g g₀ : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ G)} (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t2Space_ptsOver_of_isSeparated G.hom y
  obtain ⟨L, hL⟩ := exists_realLinear_lift (T := Points.PtsOver G.hom y) (fun x : Over.mk y ⟶ G => ⟨x.left, Over.w x⟩)
    (fun a b hab => Over.OverMorphism.ext (congrArg Subtype.val hab)) e e₀ he.1 ha he.2.1 Λ hk
    ((continuous_of_isHolTo he.2.2.1).subtype_mk _) ((continuous_of_isHolTo hh).subtype_mk _)
  have hsm : ∀ (c : ℂ) z, L (c • z) = c • L z := fun c z => he.eq_of_fderiv fun U f hU => by
    have h0 : (e₀ 0).left = (e 0).left := by rw [map_zero_of_add ha, map_zero_of_add he.1]
    have d := (differentiableAt_of_isHolTo he.2.2.1 U f hU).hasFDerivAt.restrictScalars ℝ
    have d₀ := (differentiableAt_of_isHolTo hh U f (z := 0) (by simpa only [h0] using hU)).hasFDerivAt.restrictScalars ℝ
    rw [← L.map_zero] at d
    have d₁ := d.comp 0 L.hasFDerivAt
    rw [L.map_zero] at d₁
    have e₁ : (fun b => valAt' (e b).left U f) ∘ L = fun b => valAt' (e₀ b).left U f := by
      funext b
      simp only [Function.comp_apply, hL]
    rw [e₁] at d₁
    have k := fun x => DFunLike.congr_fun (d₁.unique d₀) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at k
    rw [k, map_smul, map_smul, k]
  have hi : Function.Injective L := realLinear_injective_of_countable_ker L.toLinearMap
    (hc.mono fun x (hx : L x = 0) => by
      show e₀ x = 1
      rw [← hL, hx, map_zero_of_add he.1])
  have hsu : Function.Surjective L := realLinear_surjective_of_mod_countable L.toLinearMap (Γ := Λ)
    (Set.countable_coe_iff.1 (inferInstanceAs (Countable Λ))) fun w => by
      obtain ⟨x, hx⟩ := hs (e w)
      exact ⟨x, (hk _).1 ((eq_iff_sub_of_add he.1 _ _).1 (hx.symm.trans (hL x).symm))⟩
  exact ⟨LinearEquiv.ofBijective ⟨⟨L, L.map_add⟩, hsm⟩ ⟨hi, hsu⟩, hL⟩

end GlobalTheory.UnifPoint
end
end

