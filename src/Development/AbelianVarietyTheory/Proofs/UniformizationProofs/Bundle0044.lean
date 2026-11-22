import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IdentificationLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifLinear

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem one_pG {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (1 : T ⟶ thickObj R I e G).left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A :=
  (congrArg CommaMorphism.left (TorusCoord.im_one g (T := T))).trans (Category.assoc _ _ _)

theorem comp_q_eq_iff {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) :
    y ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] ↔
      y.left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (1 : T ⟶ thickObj R I e G) ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] :=
    MonObj.one_comp _
  rw [← h1, ← one_pG g]
  refine ⟨fun h => congrArg CommaMorphism.left (TorusCoord.im_congr g h), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem comp_fstG_hom {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) {W : Scheme.{0}} (s : Spec (CommRingCat.of R) ⟶ W) :
    y.left ≫ (fstG I e G).left ≫ G.hom ≫ s = T.hom ≫ thick R I e ≫ s := by
  rw [← Over.w y, Category.assoc]
  exact congrArg (y.left ≫ ·) (pullback.condition_assoc s)

theorem map_pG (a : G ⟶ G) (b : D.P.A ⟶ D.P.A)
    (h : (Over.pullback (thick R I e)).map a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map b) :
    ((Over.pullback (thick R I e)).map a).left ≫ g.pG.left = g.pG.left ≫ b.left := by
  have A : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      pullback.fst D.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
  have h' := congrArg (fun f => f.left ≫ pullback.fst D.P.A.hom (thick R I e)) h
  simp only [Over.comp_left, Category.assoc, A] at h'
  exact h'.trans (Category.assoc _ _ _).symm

theorem appTop_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  rw [SplitTorus.charUnit_val]
  exact (SplitTorus.res_pullU_charUnit t χ _).symm.trans (congrArg Units.val (ht χ))

theorem identification_linear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (Φ : D'.toPre.P.A ≅ D.toPre.P.A), (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG → (∀ (a : O) (y : D'.toPre.X), xe (a • y) = a • xe y) ∧ ∀ a, ιD'.onB.act a ≫ Φ.hom = Φ.hom ≫ ιD.onB.act a := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' Φ hΦ xe hval O _ _ _ _ ιD ιD' ιA ιA' ιG hl hl'
  obtain ⟨hN, -, -, hc⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  refine ⟨?_, fun a => ?_⟩
  · have hI' : I ^ (0 + 1) ≠ ⊤ := fun h => by
      rw [zero_add, pow_one] at h
      rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hI
      exact bot_ne_top hI
    have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
    have : Nonempty (Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
    have k' := (comp_q_eq_iff (U'.gt 0) _).1 (U'.gt 0).isKernel.w
    have k : (U'.gt 0).i.left ≫ (U.gt 0).pG.left =
        (splitTorus _ D'.toPre.X).hom ≫ thick R I 0 ≫ eSec D.toPre.P.A := by
      refine Eq.trans ?_ (one_pG (U.gt 0))
      rw [← hΦ]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Φ.hom.left)
        (k'.trans (one_pG (U'.gt 0)).symm)).trans (Category.assoc _ _ _))
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ≫ (U.gt 0).i = (U'.gt 0).i :=
      ⟨_, (U.gt 0).isKernel.lift_fst _ _ ((comp_q_eq_iff (U.gt 0) _).2 k)⟩
    have hchar : ∀ x, τ.left.appTop.hom (charUnit _ D.toPre.X (xe x)).val =
        (charUnit _ D'.toPre.X x).val := fun x => by
      apply TopCat.Presheaf.section_ext (Scheme.sheaf _) ⊤
      intro z hz
      obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.toPre.P.L D.toPre.P.isLB z
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.toPre.P.L D'.toPre.P.isLB z
      have v := hval 0 _ (U'.gt 0).i.left z J J' hJ hJ' (k.trans (comp_fstG_hom _ _).symm)
        (k'.trans (comp_fstG_hom _ _).symm) x
      have v₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre 0 G (U.gt 0) _ τ 1 z J hJ
        (xe x)).1
      have v₂ := (TorusCoord.val_torus_point_and_translate R I D'.toPre 0 G (U'.gt 0) _ (𝟙 _) 1 z J'
        hJ' x).1
      rw [hτ] at v₁
      rw [Category.id_comp] at v₂
      have w := congrArg Units.val (v₁.symm.trans (v.trans v₂))
      rw [Geo.Tor.gm_val _ z ⊤ trivial, Geo.Tor.gm_val _ z ⊤ trivial] at w
      exact w
    intro a y
    obtain ⟨t, ht, hi⟩ := hl.i_lin 0 (star a)
    obtain ⟨t', ht', hi'⟩ := hl'.i_lin 0 (star a)
    have : Mono (U.gt 0).i :=
      (MorphismProperty.monomorphisms _).of_isPullback (U.gt 0).isKernel.flip
        (inferInstanceAs (Mono η[thickObj R I 0 D.toPre.P.A]))
    have ht₀ : t' ≫ τ = τ ≫ t := by
      rw [← cancel_mono (U.gt 0).i, Category.assoc, Category.assoc, ← hi, hτ, ← hi',
        ← Category.assoc, hτ]
    have h := congrArg (fun f => f.left.appTop.hom (charUnit _ D.toPre.X (xe y)).val) ht₀
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [hchar, appTop_of_torusEndOf ht, appTop_of_torusEndOf ht', star_star,
      ← xe.apply_symm_apply (a • xe y), hchar, SplitTorus.charUnit_val,
      SplitTorus.charUnit_val] at h
    rw [SplitTorus.chi_injective h, xe.apply_symm_apply]
  · have := D'.toPre.P.isAb.smooth
    have := D'.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D'.toPre.P.A).2 D.toPre.P.A _ _ fun n => ?_
    have := (U'.gt n).q_flat
    have := (U'.gt n).q_surj
    have := (U'.gt n).q_affine
    have e₁ := map_pG (U.gt n) _ _ (hl.q_lin n a)
    have e₂ := map_pG (U'.gt n) _ _ (hl'.q_lin n a)
    have hE : Epi (U'.gt n).q.left := inferInstance
    refine (cancel_epi (U'.gt n).q.left).1 ?_
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    change (U'.gt n).pG.left ≫ _ = (U'.gt n).pG.left ≫ _
    have e₃ := hΦ n
    generalize (U'.gt n).pG.left = p', (U.gt n).pG.left = p at e₁ e₂ e₃ ⊢
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc, e₃, ← e₁, ← e₃, ← e₂]
    exact Category.assoc _ _ _

end GlobalTheory.UnifLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem IsCPMap.cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    {hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f} {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    (Tw : Tri w w' w'') : IsCPMap P'' P' f' F' hw' w' := by
  have key : ∀ (T : Over S''), ∃ ρ : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f),
      ρ.left = 𝟙 T.left ∧ ∀ x : T ⟶ G'', toBase hw'' x = ρ ≫ toBase hw (toBase hw' x) := fun T =>
    ⟨Over.homMk (𝟙 T.left) (by simp), rfl, fun x => Over.OverMorphism.ext
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm)⟩
  refine ⟨mul, (isGen_iff _).2 (Tw.pgen_cancel P.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)),
    fun T z J'' J' hJ'' hJ' B hB => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨ρ, hρ, e⟩ := key T
  obtain ⟨a₁, a₂, a₃⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ _ (fun _ => rfl)
  let β := toBaseHom mul T
  let A : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ :=
    fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)
  have hAB : ∀ x : T ⟶ G'', A (β x) * B x = gw w'' x.left z (J (x.left ≫ F' ≫ F)) (J'' x.left) := fun x => by
    rw [hB, ← Category.assoc]
    exact (Tw _ x.left z _ _ _ (hJ ((x.left ≫ F') ≫ F)) (hJ' (x.left ≫ F')) (hJ'' x.left)).symm
  obtain ⟨b₁, b₂, b₃⟩ := h''.vals T z J'' J hJ'' hJ (fun x => A (β x) * B x) hAB
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [map_one, ← Category.assoc, _root_.mul_assoc] at b₁
    exact mul_left_cancel (a := A 1) (a₁.symm.trans b₁)
  · have a : val P.sym ((x.left ≫ F') ≫ F) z J * A (β x) = A (β x)⁻¹ * val P'.sym (x.left ≫ F') z J' := a₂ (β x)
    have b := b₂ x
    rw [map_inv, ← Category.assoc, ← _root_.mul_assoc, a, _root_.mul_assoc, _root_.mul_assoc] at b
    exact mul_left_cancel b
  · have c : @_root_.id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x)
        (toBase hw'' y) (toBase hw'' u)) = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := by
      have e' : (lift (toBase hw'' x) (lift (toBase hw'' y) (toBase hw'' u))).left =
          (lift (toBase hw (β x)) (lift (toBase hw (β y)) (toBase hw (β u)))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift, Over.comp_left, hρ]; exact Category.id_comp _
      exact congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e'
    obtain ⟨C, hC⟩ : ∃ C : (T.left.presheaf.stalk z)ˣ, C = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ : ∃ C' : (T.left.presheaf.stalk z)ˣ, C' = cubV P'.c (T := Over.mk (T.hom ≫ f')) z J'
        (β x) (β y) (β u) := ⟨_, rfl⟩
    have a : C * A (β x * β y) * A (β x * β u) * A (β y * β u) * A 1 =
        A (β x * β y * β u) * A (β x) * A (β y) * A (β u) * C' := by
      rw [hC, hC']; exact a₃ (β x) (β y) (β u)
    have b := b₃ x y u
    rw [c.trans hC.symm] at b
    simp only [map_mul, map_one] at b
    have g : C' * B (x * y) * B (x * u) * B (y * u) * B 1 =
        B (x * y * u) * B x * B y * B u * cubV P''.c z J'' x y u := by
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    rw [hC'] at g
    exact g

theorem isCPMap_comp_cancel :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by
  intro S S' S'' f f' G _ _ G' _ _ G'' _ _ P P' P'' F hw w F' hw' hw'' h
  refine ⟨fun w' h' => ?_, fun mul w'' h'' => ?_⟩
  · obtain ⟨w'', Tw, H⟩ := h.exists_comp h' hw''
    exact ⟨w'', H, Tw⟩
  · obtain ⟨w', Tw⟩ := Geo.Tor.exists_cancel P.L.isLB w w'' ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)
      P'.L.isLB P''.L.isLB
    exact ⟨w', h.cancel h'' mul Tw, Tw⟩

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullLinear

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem map_left_fst {S T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem ext_of_iso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' Z : Over S'}
    (e : A' ≅ (Over.pullback f).obj A) {a b : Z ⟶ A'}
    (h : a.left ≫ e.hom.left ≫ pullback.fst A.hom f = b.left ≫ e.hom.left ≫ pullback.fst A.hom f) :
    a = b := by
  rw [← cancel_mono e.hom]
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simpa only [Over.comp_left, Category.assoc] using h
  · exact (Over.w (a ≫ e.hom)).trans (Over.w (b ≫ e.hom)).symm

theorem ext_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {Z : Over S'}
    {a b : Z ⟶ (Over.pullback f).obj A}
    (h : a.left ≫ pullback.fst A.hom f = b.left ≫ pullback.fst A.hom f) : a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

theorem act_proj {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) {u : A ⟶ A} {u' : A' ⟶ A'}
    (h : u' ≫ e = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e.left ≫ pullback.fst A.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem pG_left : g.pG.left = g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) := rfl

theorem im_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e) :
    im g (τ ≫ g.i) = 1 := by
  have := g.q_hom
  rw [← im_one g]
  refine im_congr g ?_
  rw [Category.assoc, g.isKernel.w, MonObj.one_comp, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem exists_torus_of_im {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : Z ⟶ thickObj R I e G) (h : im g y = 1) : ∃ τ : Z ⟶ WeightPf.Te D I e, τ ≫ g.i = y := by
  have h1 : y ≫ g.q = (1 : Z ⟶ thickObj R I e G) ≫ g.q := by
    refine ext_of_pullback _ ?_
    have := congrArg (·.left) (h.trans (im_one g).symm)
    exact ((Category.assoc _ _ _).trans this).trans (Category.assoc _ _ _).symm
  obtain ⟨τ, hτ⟩ := exists_torus g y 1 h1
  exact ⟨τ, by rw [hτ, _root_.mul_one]⟩

theorem prod_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e)
    (χ : D.X) {U : Type} [CommGroup U] (f : (Z.left ⟶ D.P.A.left) → U) :
    ∏ k, f ((τ ≫ g.i).left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, (τ ≫ g.i).left ≫ D.Oφ g.pG χ k = D.Oφ (im g (τ ≫ g.i)) χ k := fun k =>
    WeightPf.Oφ_comp ((Over.map (thick R I e)).map (τ ≫ g.i)) g.pG χ k
  simp only [e0]
  rw [Fin.prod_univ_four, im_torus]
  change f ((1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A) * cPt Z χ).left ^ (-1 : ℤ) *
    f (cPt Z χ).left ^ (1 : ℤ) * f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (1 : ℤ) *
    f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  rw [_root_.one_mul, zpow_neg_one, zpow_neg_one, zpow_one, zpow_one, inv_mul_cancel, _root_.one_mul,
    mul_inv_cancel]

theorem torusEndOf_iff {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) :
    TorusEndOf X h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X),
      gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} {D : DegPre R} {D' : DegPre R'} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I' D' e G') {F : D'.P.A.left ⟶ D.P.A.left}
  {h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left}

theorem char_eq (w : LB.Iso D'.P.L (D.P.L.pull F)) {x' : D'.X} {x : D.X}
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    (hm : PMaps w (D'.Oφ g'.pG x') (D.Oφ g.pG x) Oinvε (g'.t x') (g.t x) h)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))}
    {s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))}
    (τ' : Z' ⟶ WeightPf.Te D' I' e) (τ : Over.mk s ⟶ WeightPf.Te D I e)
    (hτ : (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h) (z : Z'.left) :
    gm (Y := Z'.left) τ.left z ⊤ (charUnit _ D.X x) = gm τ'.left z ⊤ (charUnit _ D'.X x') := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
  obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
  have h₁ := (val_torus_point_and_translate R I D e G g (Over.mk s) τ 1 z J hJ x).1
  have h₂ := (val_torus_point_and_translate R' I' D' e G' g' Z' τ' 1 z J' hJ' x').1
  have h₃ := hm Z'.left (τ' ≫ g'.i).left z
    (fun k => J (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => J' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
    (fun k => hJ (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => hJ' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
  rw [prod_torus g' τ' x' (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at h₃
  refine h₁.symm.trans (Eq.trans ?_ (h₃.trans h₂))
  rw [hτ]
  exact val_of (g.t x) ((τ' ≫ g'.i).left ≫ h) z J _ (fun k => by
    rw [Category.assoc, Category.assoc, hψ k])

theorem exists_point {x' : D'.X} {x : D.X} (hp : g'.pG.left ≫ F = h ≫ g.pG.left)
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))} (τ' : Z' ⟶ WeightPf.Te D' I' e) :
    ∃ (s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (τ : Over.mk s ⟶ WeightPf.Te D I e),
      (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h := by
  let y : Over.mk (((τ' ≫ g'.i).left ≫ h) ≫ (thickObj R I e G).hom) ⟶ thickObj R I e G :=
    Over.homMk ((τ' ≫ g'.i).left ≫ h) rfl
  have h1 : (τ' ≫ g'.i).left ≫ g'.pG.left = (τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' 3 := by
    refine (congrArg (·.left) (im_torus g' τ')).trans ?_
    exact (WeightPf.Oφ_comp ((Over.map (thick R' I' e)).map (τ' ≫ g'.i)) g'.pG x' 3).symm
  have h2 : im g y = 1 := by
    refine Over.OverMorphism.ext ?_
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map y) g.pG x 3)
    change ((τ' ≫ g'.i).left ≫ h) ≫ g.pG.left = ((τ' ≫ g'.i).left ≫ h) ≫ D.Oφ g.pG x 3
    rw [Category.assoc, Category.assoc, ← hp, ← hψ, ← Category.assoc, h1, Category.assoc]
  obtain ⟨τ, hτ⟩ := exists_torus_of_im g y h2
  exact ⟨_, τ, congrArg (·.left) hτ⟩

end Two

theorem oLinear_of_isPullUnif : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) → (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) → (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) → U'.OLinear O ιD' ιA' ιG' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ U U' hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    hlin hG hgen hx hB
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ) (a : O), ((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := by
    intro e a
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom (hG a), Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ) (a : O), (Over.pullback (thick R' I' e)).map (ιG'.act a) ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map (ιD'.onB.act a) := by
    intro e a
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ g u
      rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
      rw [← k, ← hlin.q_lin e a]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ ιD'.onB.act a := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ (ιD'.onB.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom (hB a), (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine ⟨hgen, hq, fun e a => ?_⟩
  obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
  have := ιD'.onB.hom a
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (star a • χ)).1 ((hpt e).2 (star a • χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.PullLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KerAppEqMapAppLEOfIsPullback
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem ker_app_eq_map_appLE_of_isPullback {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem isPullback_red_of_ker_app_le_map (A : Type) [CommRing A] (J : Ideal A)
    (B₀ B : Scheme.{0}) (j : B₀ ⟶ B) (s₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J)))
    (s : B ⟶ Spec (CommRingCat.of A)) (hj : IsClosedImmersion j) (w : j ≫ s = s₀ ≫ red J)
    (hloc : ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ IsAffineOpen V ∧ RingHom.ker (j.app V).hom ≤
      J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ V le_top).hom) :
    IsPullback j s₀ s (red J) := by
  have hr : IsClosedImmersion (red J) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hp : IsClosedImmersion (pullback.fst s (red J)) := inferInstance
  have hl : pullback.lift j s₀ w ≫ pullback.fst s (red J) = j := pullback.lift_fst _ _ _
  have hker : j.ker = (pullback.fst s (red J)).ker := by
    refine le_antisymm ?_ ?_
    · choose V hb hV hle using hloc
      have hcov : ⨆ b, ((⟨V b, hV b⟩ : B.affineOpens) : B.Opens) = ⊤ :=
        eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨b, hb b⟩
      refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun b ↦ ⟨V b, hV b⟩) hcov fun b ↦ ?_
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
      have e := ker_app_eq_map_appLE_of_isPullback
        (β := CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective
        (IsPullback.of_hasPullback s (red J)) (hV b)
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at e
      exact (hle b).trans e.ge
    · have := (pullback.lift j s₀ w).le_ker_comp (pullback.fst s (red J))
      rwa [hl] at this
  have := IsClosedImmersion.isIso_of_ker_eq j (pullback.fst s (red J)) _ hl hker
  exact .of_iso_pullback ⟨w⟩ (asIso (pullback.lift j s₀ w)) hl (pullback.lift_snd _ _ _)

end GlobalTheory
end

