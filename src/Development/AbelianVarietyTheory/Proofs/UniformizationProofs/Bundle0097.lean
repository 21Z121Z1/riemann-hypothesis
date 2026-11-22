import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FormallyUnramifiedOfIsFinite
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteOnePoint

theorem isIso_of_formallyUnramified {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → p = s) : IsIso f := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : IsOpenImmersion s :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal f))) (by rw [hs]; infer_instance)
  have := LocallyOfFiniteType.jacobsonSpace f
  have hsurj : Surjective s := ⟨fun x => by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.range s)ᶜ) ⟨x, hx⟩
      s.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
    refine hc ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [← h _ (pointOfClosedPoint_comp f c hc')]
    exact pointOfClosedPoint_apply f c hc' _⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).2 ⟨ho, hsurj⟩
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

theorem formallyUnramified_of_isFinite {K : Type} [Field K] [CharZero K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (hf : IsFinite G.hom) :
    FormallyUnramified G.hom := by
  obtain ⟨N, hN, h⟩ := FiniteFlatKilled.main K G hf inferInstance
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h1 : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have h2 := formallyUnramified_mulA _ G N hu
  have h3 : (mulA G N).left = G.hom ≫ η[G].left := by
    rw [show mulA G N = 1 from h, Hom.one_def]
    rfl
  rw [h3] at h2
  exact FormallyUnramified.of_comp G.hom η[G].left

theorem main : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (H : Over S) (j : H ⟶ B), Mono j → IsFinite H.hom → (∃ y : 𝟙_ _ ⟶ H, y ≫ j = 1) → (∀ (T : Over S) (x y : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j) * (y ≫ j)⁻¹) → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (t : Spec (CommRingCat.of K) ⟶ S), (∀ x : Over.mk t ⟶ H, x ≫ j = 1) → ∀ (T : Over S) (_ : T ⟶ Over.mk t) (y : T ⟶ H), y ≫ j = 1 := by
  intro S B _ _ H j hj hf ⟨e, he⟩ hsub K _ _ _ t hpt T a y
  have he' : ∀ T : Over S, (toUnit T ≫ e) ≫ j = 1 := fun T => by
    rw [Category.assoc, he, MonObj.comp_one]
  have hinv : ∀ (T : Over S) (x : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j)⁻¹ := fun T x => by
    obtain ⟨z, hz⟩ := hsub T (toUnit T ≫ e) x
    exact ⟨z, by rw [hz, he', _root_.one_mul]⟩
  obtain ⟨i, hi⟩ := hinv H (𝟙 H)
  obtain ⟨w, hw⟩ := hinv (H ⊗ H) (snd H H)
  obtain ⟨m, hm⟩ := hsub (H ⊗ H) (fst H H) w
  obtain ⟨_, _⟩ := ReducedSubgroup.exists_grpObj_of_mono j e m i
    (by rw [he, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    (by
      rw [hm, hw, inv_inv, Hom.mul_def]
      congr 1)
    (by rw [hi, Category.id_comp, Hom.inv_def])
  haveI : IsCommMonObj H :=
    ⟨by rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩
  have hfin : IsFinite (pullback.snd H.hom t) := inferInstance
  have hunr : FormallyUnramified (pullback.snd H.hom t) :=
    formallyUnramified_of_isFinite ((Over.pullback t).obj H) hfin
  have hiso : IsIso (pullback.snd H.hom t) := by
    refine isIso_of_formallyUnramified _
      (pullback.lift (toUnit (Over.mk t) ≫ e).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) fun p hp => ?_
    let x : Over.mk t ⟶ H := Over.homMk (p ≫ pullback.fst H.hom t) (by
      change (p ≫ pullback.fst H.hom t) ≫ H.hom = t
      rw [Category.assoc, pullback.condition, reassoc_of% hp])
    have hx : x = toUnit _ ≫ e := by rw [← cancel_mono j, hpt, he']
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hx]
      rfl
    · rw [pullback.lift_snd, hp]
  have key : ∀ y₁ y₂ : T ⟶ H, y₁ = y₂ := fun y₁ y₂ => by
    have h : pullback.lift y₁.left a.left ((Over.w y₁).trans (Over.w a).symm) =
        pullback.lift (f := H.hom) (g := t) y₂.left a.left ((Over.w y₂).trans (Over.w a).symm) := by
      rw [← cancel_mono (pullback.snd H.hom t)]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    ext1
    exact (pullback.lift_fst _ _ _).symm.trans
      ((h =≫ pullback.fst H.hom t).trans (pullback.lift_fst _ _ _))
  rw [key y (toUnit T ≫ e), he']

end FiniteOnePoint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfProportional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjUniq

theorem hom_eq_of_proportional : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (T : Scheme.{0}) (φ ψ : T ⟶ Z), φ ≫ f = ψ ≫ f → (∀ z k k' i i', φ z ∈ H.U k → ψ z ∈ H.U k' → gs φ z (H.U k) ((s i).f k) * gs ψ z (H.U k') ((s i').f k') = gs φ z (H.U k) ((s i').f k) * gs ψ z (H.U k') ((s i).f k')) → φ = ψ := by
  intro R _ Z f H n s hH hs T φ ψ hf h
  choose r hr hsurj using fun i => (hs.2 i).2
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
    obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show ψ z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk] at hz
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i') ψ z hk'] at hi'
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk']
    have hu := hz.mul hi'
    rw [h z k k' i i' hk hk'] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm
    fun i z hz a => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (φ z)
  obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j => by
    have e₁ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) φ z hz hk
    have e₂ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) ψ z hz' hk'
    have u₁ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk).1 hz
    have u₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk').1 hz'
    have e := h z k k' j i hk hk'
    rw [e₁, e₂] at e
    refine (u₁.mul u₂).mul_right_cancel ?_
    linear_combination e
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, MapUniq.gs_cst f φ z _ hz, MapUniq.gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add, gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.ProjUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfThickeningPoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.isProper_tensorObj_over {S : Scheme.{0}} {Z B : Over S} (hZ : IsProper Z.hom)
    (hB : IsProper B.hom) : IsProper (Z ⊗ B).hom := by
  simp only [Over.tensorObj_hom]
  infer_instance

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma hom_ext_of_thickenings (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X B : Over (Spec (CommRingCat.of V))} [IsProper X.hom]
    [IsProper B.hom] (f g : X ⟶ B)
    (h : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (t : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ X), t ≫ f = t ≫ g) :
    f = g := by
  refine _root_.GlobalTheory.hom_eq_of_thickenings_of_isProper V (IsLocalRing.maximalIdeal V) ?_ X B f g ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top
  · intro e
    exact congrArg Over.Hom.left (h e (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj V _ e X) (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG _ e X))

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.grpObj_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) (Y (e + 1)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) [IsProper B.hom], (∀ e, IsPullback (b e) (Y e).hom B.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) → ∃ _ : GrpObj B, (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) B (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V _ e) (b e)) ∧ ((∀ e, IsCommMonObj (Y e)) → IsCommMonObj B) := by
  intro V _ _ _ Y _ β _ B b _ hpb _ mu io un hY
  have lft : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B),
      ∃ x : T ⟶ Y e, u.left = x.left ≫ b e := by
    intro e T u
    refine ⟨Over.homMk ((hpb e).lift u.left T.hom (by simpa using Over.w u))
      ((hpb e).lift_snd _ _ _), ?_⟩
    simp
  have hmul : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u v : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x y : T ⟶ Y e),
      u.left = x.left ≫ b e → v.left = y.left ≫ b e → (lift u v ≫ mu).left = (x * y).left ≫ b e :=
    fun e T u v x y hu hv => (hY e T x y u v hu hv).1
  have hinv : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x : T ⟶ Y e),
      u.left = x.left ≫ b e → (u ≫ io).left = x⁻¹.left ≫ b e :=
    fun e T u x hu => (hY e T x x u u hu hu).2.1
  have hone : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left =
        (1 : T ⟶ Y e).left ≫ b e := by
    intro e T
    obtain ⟨u, hu⟩ : ∃ u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B,
        u.left = (1 : T ⟶ Y e).left ≫ b e :=
      ⟨Over.homMk ((1 : T ⟶ Y e).left ≫ b e) (by
        simp only [Over.mk_hom, Category.assoc, (hpb e).w]
        rw [← Category.assoc, Over.w]), rfl⟩
    exact (hY e T 1 1 u u hu hu).2.2
  have hB2 : IsProper (B ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over inferInstance inferInstance
  have hB3 : IsProper ((B ⊗ B) ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over hB2 inferInstance
  have hB1 : IsProper (B ⊗ 𝟙_ _).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over inferInstance (by simp; infer_instance)
  have hB1' : IsProper (𝟙_ _ ⊗ B).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over (by simp; infer_instance) inferInstance
  letI : MonObj B :=
    { one := un
      mul := mu
      one_mul := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ fst _ _) (toUnit _)]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        ext
        rw [hmul e T _ _ 1 x (hone e T) hx, _root_.one_mul, hx]
      mul_one := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ snd _ _) (toUnit _)]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        ext
        rw [hmul e T _ _ x 1 hx (hone e T), _root_.mul_one, hx]
      mul_assoc := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (lift (t ≫ fst _ _ ≫ fst _ _) (t ≫ fst _ _ ≫ snd _ _)) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;>
            [apply CartesianMonoidalCategory.hom_ext; skip] <;> simp
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        ext
        rw [hmul e T _ _ (x * y) z (hmul e T _ _ x y hx hy) hz,
          hmul e T _ _ x (y * z) hx (hmul e T _ _ y z hy hz), _root_.mul_assoc] }
  letI : GrpObj B :=
    { inv := io
      left_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x⁻¹ x (hinv e T t x hx) hx).trans ?_
        rw [inv_mul_cancel, ← hone e T]
        rfl
      right_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x x⁻¹ hx (hinv e T t x hx)).trans ?_
        rw [mul_inv_cancel, ← hone e T]
        rfl }
  refine ⟨this, fun e => ⟨hpb e, fun T x y x₀ y₀ hx hy => hmul e T x₀ y₀ x y hx hy⟩, fun hc => ?_⟩
  exact
    { mul_comm := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht]
        simp only [lift_braiding_hom_assoc]
        ext
        have := hc e
        refine (hmul e T _ _ y x hy hx).trans ?_
        rw [_root_.mul_comm]
        exact (hmul e T _ _ x y hx hy).symm }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TrivTwist

variable {X Y : Scheme.{0}}

theorem gm_pull_g (A : LB X) (f : Y ⟶ X) (y : Y) (i j : A.ι) (hi : f y ∈ A.U i) (hj : f y ∈ A.U j) :
    gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j)) ((A.pull f).g (fun _ => i) (fun _ => j)) =
      gm f y (A.U i ⊓ A.U j) (A.g i j) := by
  have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (A.g i j))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) f y (A.U i ⊓ A.U j) ⟨hi, hj⟩ _).trans (by rw [Category.id_comp]))

theorem isGen_pull_iff (A : LB X) (f : Y ⟶ X) (t : LB.Gen (A.pull f)) :
    t.IsGen ↔ ∀ (i j : A.ι) (y : Y), f y ∈ A.U i → f y ∈ A.U j →
      gm (𝟙 Y) y ((A.pull f).U (fun _ => i)) (t.s (fun _ => i)) =
        gm f y (A.U i ⊓ A.U j) (A.g i j) * gm (𝟙 Y) y ((A.pull f).U (fun _ => j)) (t.s (fun _ => j)) := by
  constructor
  · intro h i j y hi hj
    have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) :=
      ⟨mem_pull.2 hi, mem_pull.2 hj⟩
    have := congrArg (gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j))) (h (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ y _ hp, gm_res _ y _ hp, gm_pull_g A f y i j hi hj] at this
    exact this
  · intro h I J
    refine unit_ext fun y hy => ?_
    have hi := mem_pull.1 hy.1
    have hj := mem_pull.1 hy.2
    have := h (I PUnit.unit) (J PUnit.unit) y hi hj
    rw [← gm_pull_g A f y _ _ hi hj] at this
    exact (gm_res _ y _ hy _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hy _))).symm)

theorem gm_div_g_one (M N : LB X) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) (y : Y) (p q : M.ι × N.ι)
    (hp : f y ∈ (LB.div M N).U p) (hq : f y ∈ (LB.div M N).U q) :
    gm f y ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) = gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  have hm : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res f y _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm _)))).trans ?_)
  rw [hN, map_one, inv_one, _root_.mul_one]

theorem triv_pull_div_iff (M N : LB X) (hc : ∀ x : X, ∃ k, x ∈ N.U k) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) :
    Triv (M.pull f) ↔ Triv ((LB.div M N).pull f) := by
  have hle : ∀ p : M.ι × N.ι, ((LB.div M N).pull f).U (fun _ => p) ≤ (M.pull f).U (fun _ => p.1) :=
    fun p y hy => mem_pull.2 (mem_pull.1 hy).1
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun P => res (hle (P PUnit.unit)) (t.s (fun _ => (P PUnit.unit).1))⟩, (isGen_pull_iff _ f _).2 ?_⟩
    intro p q y hp hq
    rw [gm_div_g_one M N hN f y p q hp hq]
    exact (gm_res (𝟙 Y) y (hle p) (mem_pull.2 hp) _).trans (((isGen_pull_iff M f t).1 ht p.1 q.1 y hp.1 hq.1).trans
      (congrArg _ (gm_res (𝟙 Y) y (hle q) (mem_pull.2 hq) _).symm))
  · rintro ⟨c, hc'⟩
    have H : ∀ (p q : M.ι × N.ι) (y : Y), f y ∈ (LB.div M N).U p → f y ∈ (LB.div M N).U q →
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => p)) (c.s (fun _ => p)) =
          gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
            gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => q)) (c.s (fun _ => q)) := fun p q y hp hq => by
      rw [← gm_div_g_one M N hN f y p q hp hq]
      exact (isGen_pull_iff _ f c).1 hc' p q y hp hq
    have glue : ∀ i : M.ι, ∃ s : Γ(Y, (M.pull f).U (fun _ => i))ˣ, ∀ k : N.ι,
        res (hle (i, k)) s = c.s (fun _ => (i, k)) := fun i =>
      glue_unit _ (fun k => ((LB.div M N).pull f).U (fun _ => (i, k))) (fun k => hle (i, k))
        (fun y hy => by
          obtain ⟨k, hk⟩ := hc (f y)
          exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 ⟨mem_pull.1 hy, hk⟩⟩)
        (fun k => c.s (fun _ => (i, k))) (fun k k' y hy => by
          have h₁ := mem_pull.1 hy.1
          have h₂ := mem_pull.1 hy.2
          have e := mul_eq_right.1 (H (i, k) (i, k) y h₁ h₁).symm
          have e' := H (i, k) (i, k') y h₁ h₂
          exact e'.trans ((congrArg (· * _) e).trans (_root_.one_mul _)))
    choose s hs using glue
    refine ⟨⟨fun I => s (I PUnit.unit)⟩, (isGen_pull_iff M f _).2 fun i j y hi hj => ?_⟩
    obtain ⟨k, hk⟩ := hc (f y)
    have v : ∀ a, f y ∈ M.U a → gm (𝟙 Y) y ((M.pull f).U (fun _ => a)) (s a) =
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => (a, k))) (c.s (fun _ => (a, k))) := fun a ha =>
      (gm_res (𝟙 Y) y (hle (a, k)) (mem_pull.2 ⟨ha, hk⟩) _).symm.trans (congrArg _ (hs a k))
    exact (v i hi).trans ((H (i, k) (j, k) y ⟨hi, hk⟩ ⟨hj, hk⟩).trans (congrArg _ (v j hj).symm))

theorem linComb_pw_zero_g (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    (LB.LinComb (pw L 0) φ ε).g i j = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (pw L 0).g (i k) (j k) = 1 := zpow_zero _
  exact (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ e).trans (map_one _))).trans (map_one _))).trans (one_zpow _)

theorem inK_iff_trivial_twist : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → (pw L 0).IsLB ∧ (∃ u : LB.Gen (abelian₂ B (pw L 0)), u.IsGen) ∧ ∀ (O : LB B.left), O = pw L 0 → ∀ (T : Over S) (x : T ⟶ B), InK B L x ↔ (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) := by
  intro S B _ L hL
  refine ⟨isLB_pw hL 0, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, ?_⟩
  · exact (map_one _).trans
      ((congrArg₂ (· * ·) (linComb_pw_zero_g L _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · rintro O rfl T x
    refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
    refine triv_pull_div_iff _ _ (fun y => ?_) (fun i j => linComb_pw_zero_g L _ _ i j) _
    obtain ⟨k, hk⟩ := exists_chart (isLB_pw hL 0) ((snd T B).left y)
    exact ⟨fun _ => k, mem_pull.2 hk⟩

end GlobalTheory.UU.TrivTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

variable {S : Scheme.{0}}

def powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) : PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : IsCommMonObj A' := PowGrp.comm_of_isPowGrp p P.isAb.comm
  { A := A'
    isAb := (PowGrp.powers S A' P.A j p).2.2.2.1 P.isAb
    g := j * P.g
    smoothDim := (PowGrp.powers S A' P.A j p).2.2.1 P.g P.smoothDim
    L := boxLB P.L p.pr
    isLB := LB.isLB_linComb P.isLB _ _
    rigid := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).1 P.rigid
    sym := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).2 P.sym
    ample := T.relAmple_externalTensorPower_groupPower S A' P.A j p P.L P.isLB P.ample
    ktriv := T.kTriv_external_tensor_power_lineBundle S A' P.A j p P.L P.isLB P.ktriv }

def isPowPolAV_powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    IsPowPolAV (powPolOf P A' p) P j where
  toIsPowGrp := p
  w := CubePf.idIsoL (boxLB P.L p.pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb P.isLB _ _)

def powPol (P : PolAV S) (j : ℕ) : PolAV S :=
  powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

def isPowPolAV_powPol (P : PolAV S) (j : ℕ) : IsPowPolAV (powPol P j) P j :=
  isPowPolAV_powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

@[simp] theorem powPolOf_A (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    (powPolOf P A' p).A = A' := rfl

@[simp] theorem powPolOf_g (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    (powPolOf P A' p).g = j * P.g := rfl

@[simp] theorem powPol_A (P : PolAV S) (j : ℕ) : (powPol P j).A = powObj P.A j := rfl

@[simp] theorem powPol_g (P : PolAV S) (j : ℕ) : (powPol P j).g = j * P.g := rfl

theorem exists_powPolAV : ∀ (S : Scheme.{0}) (P : PolAV S) (j : ℕ),
    ∃ (P' : PolAV S) (_ : IsPowPolAV P' P j), P'.g = j * P.g :=
  fun _ P j => ⟨powPol P j, isPowPolAV_powPol P j, rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
end

