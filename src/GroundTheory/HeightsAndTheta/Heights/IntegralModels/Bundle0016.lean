import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

theorem glueLat_frame {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
    {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
    {i : τ} (hi : x i ≠ 0) (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x i) ∧ (∀ l, c l ∈ chartRing ℤ x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) (f l) := by
  refine exists_frame_cover _ r _ fun Q hQ => ?_
  by_cases hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∈ Q
  · rw [primeProd, Int.cast_prod] at hmQ
    obtain ⟨p, hp, hpQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ.isPrime)).1 hmQ
    exact frame_at_prime hi hSR Q hQ.isPrime ⟨p, hp⟩ hpQ
  · exact frame_away hi hSR Q hQ.isPrime hmQ

theorem ChartGlue.proof : ChartGlue.Statement := by
  intro Ω _ _ τ _ x r E _ _ S o₀ _ _ _ _ o _ _ _ _ B₀ Bp hSR
  refine ⟨{ lat := glueLat B₀ Bp
            stable := glueLat_stable
            frame := fun i hi => glueLat_frame hi fun p => hSR p i hi
            overlap := glueLat_overlap }, fun i hi => ⟨mem_B₀_iff fun p => hSR p i hi,
              fun p v => mem_Bp_iff (fun p => hSR p i hi) p v⟩⟩

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDescendHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace DescendHom

section General

variable {T Y Z : Scheme.{0}}

lemma hom_app_res {M N : Y.Modules} (χ : M ⟶ N) {U V : Y.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    χ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (χ.app U x) := by
  have h := congrArg (fun f => f.hom x) (χ.mapPresheaf.naturality i.op)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h

lemma res_injective_of_eq (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : U ⟶ V) :
    Function.Injective (M.presheaf.map i.op) := by
  have : i = eqToHom h := Subsingleton.elim _ _
  subst this
  exact (ConcreteCategory.bijective_of_isIso _).1

lemma pullSectionOn_naturality (g : T ⟶ Y) {M N : Y.Modules} (χ : M ⟶ N) (V : Y.Opens)
    (m : Γ(M, V)) :
    ((Scheme.Modules.pullback g).map χ).app (g ⁻¹ᵁ V) (pullSectionOn g M V m) =
      pullSectionOn g N V (χ.app V m) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality χ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V).hom m) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm

lemma pullSectionOn_comp_inv (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).inv.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn (f ≫ h) M O m) =
        pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m) := by
  have hu := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction h).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ h)) (Scheme.Modules.pullbackComp f h).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom m) hu
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm

lemma pullSectionOn_comp_hom (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).hom.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m)) = pullSectionOn (f ≫ h) M O m := by
  rw [← pullSectionOn_comp_inv, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app]
  rfl

lemma pullSectionOn_openImmersion (ι : Z ⟶ Y) [IsOpenImmersion ι] (M : Y.Modules) (O : Y.Opens)
    (m : Γ(M, O)) :
    pullSectionOn ι M O m = ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M).app (ι ⁻¹ᵁ O)
      ((M.restrictAppIso ι (ι ⁻¹ᵁ O)).inv (M.presheaf.map (homOfLE (ι.image_preimage_le O)).op m)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction ι)
    (Scheme.Modules.pullbackPushforwardAdjunction ι) M
  rw [pullSectionOn, ← h]
  rfl

lemma hom_eq_of_pullSectionOn (g : T ⟶ Y) (R : Y.Opens) (hR : g ⁻¹ᵁ R = ⊤) {F G : Y.Modules}
    (χ₁ χ₂ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (h : ∀ V : Y.Opens, V ≤ R → ∀ s : Γ(F, V),
      χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) :
    χ₁ = χ₂ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  ext V s
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app]
  change χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)
  have hE : g ⁻¹ᵁ (V ⊓ R) = g ⁻¹ᵁ V := le_antisymm ((Opens.map g.base).monotone inf_le_left)
    (fun x hx => ⟨hx, by
      have : x ∈ g ⁻¹ᵁ R := by rw [hR]; trivial
      exact this⟩)
  apply res_injective_of_eq _ hE (homOfLE hE.le)
  rw [← hom_app_res, ← hom_app_res]
  rw [← pullSectionOn_res g F (inf_le_left : V ⊓ R ≤ V) (homOfLE hE.le) s]
  exact h _ inf_le_right _

lemma pullbackHomAlong_rfl (ι : Z ⟶ Y) (g' : T ⟶ Z) {F G : Y.Modules}
    (ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G) :
    pullbackHomAlong (rfl : g' ≫ ι = g' ≫ ι) ψ = (Scheme.Modules.pullbackComp g' ι).inv.app F ≫
      (Scheme.Modules.pullback g').map ψ ≫ (Scheme.Modules.pullbackComp g' ι).hom.app G := by
  simp [pullbackHomAlong, pullbackCompIso, Scheme.Modules.pullbackCongr]

end General

section Descend

variable {T Y Z : Scheme.{0}} (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) {F G : Y.Modules}
  (φ : (Scheme.Modules.pullback (g' ≫ ι)).obj F ⟶ (Scheme.Modules.pullback (g' ≫ ι)).obj G)
  (hinj : ∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn (g' ≫ ι) G V))
  (t : ∀ V : Y.Opens, V ≤ ι.opensRange → Γ(F, V) → Γ(G, V))
  (ht : ∀ (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)),
    pullSectionOn (g' ≫ ι) G V (t V hV s) =
      φ.app ((g' ≫ ι) ⁻¹ᵁ V) (pullSectionOn (g' ≫ ι) F V s))
include hinj ht

lemma t_res {V W : Y.Opens} (hV : V ≤ ι.opensRange) (h : W ≤ V) (s : Γ(F, V)) :
    t W (h.trans hV) (F.presheaf.map (homOfLE h).op s) =
      G.presheaf.map (homOfLE h).op (t V hV s) := by
  apply hinj W (h.trans hV)
  rw [ht, pullSectionOn_res (g' ≫ ι) F h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)),
    pullSectionOn_res (g' ≫ ι) G h (homOfLE ((Opens.map (g' ≫ ι).base).monotone h)), ht,
    hom_app_res]

lemma t_add {V : Y.Opens} (hV : V ≤ ι.opensRange) (a b : Γ(F, V)) :
    t V hV (a + b) = t V hV a + t V hV b := by
  apply hinj V hV
  rw [map_add, ht, ht, ht, map_add, map_add]

lemma t_zero {V : Y.Opens} (hV : V ≤ ι.opensRange) : t V hV 0 = 0 := by
  apply hinj V hV
  rw [ht, map_zero, map_zero, map_zero]

lemma t_smul {V : Y.Opens} (hV : V ≤ ι.opensRange) (r : Γ(Y, V)) (a : Γ(F, V)) :
    t V hV (r • a) = r • t V hV a := by
  apply hinj V hV
  rw [ht, pullSectionOn_smul, Scheme.Modules.Hom.app_smul, ← ht, pullSectionOn_smul]

def restrictHom : F.restrict ι ⟶ G.restrict ι :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => t (ι ''ᵁ U.unop) (ι.image_le_opensRange _) s
          map_zero' := t_zero ι g' φ hinj t ht _
          map_add' := t_add ι g' φ hinj t ht _ }
      naturality := fun U V i => by
        ext s
        exact t_res ι g' φ hinj t ht (ι.image_le_opensRange _) (ι.image_mono (leOfHom i.unop)) s }
    (fun U r s => t_smul ι g' φ hinj t ht _ ((ι.appIso U.unop).inv r) s)

lemma restrictHom_app (U : Z.Opens) (s : Γ(F, ι ''ᵁ U)) :
    (restrictHom ι g' φ hinj t ht).app U s = t (ι ''ᵁ U) (ι.image_le_opensRange _) s :=
  rfl

def descendPsi : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G :=
  (Scheme.Modules.restrictFunctorIsoPullback ι).inv.app F ≫ restrictHom ι g' φ hinj t ht ≫
    (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app G

lemma descendPsi_pull (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)) :
    (descendPsi ι g' φ hinj t ht).app (ι ⁻¹ᵁ V) (pullSectionOn ι F V s) =
      pullSectionOn ι G V (t V hV s) := by
  rw [pullSectionOn_openImmersion ι F, pullSectionOn_openImmersion ι G, descendPsi,
    ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app_assoc,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact t_res ι g' φ hinj t ht hV (ι.image_preimage_le V) s

end Descend

end DescendHom

theorem DescendHom.proof : DescendHom.Statement := by
  intro T Y Z ι _ g' g e F G φ hinj hex
  subst e
  choose t ht using hex
  refine ⟨DescendHom.descendPsi ι g' φ hinj t ht, ?_⟩
  have hR : (g' ≫ ι) ⁻¹ᵁ ι.opensRange = ⊤ := top_le_iff.1 fun x _ => ⟨g'.base x, rfl⟩
  refine DescendHom.hom_eq_of_pullSectionOn (g' ≫ ι) ι.opensRange hR _ _ fun V hV s => ?_
  rw [DescendHom.pullbackHomAlong_rfl]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [DescendHom.pullSectionOn_comp_inv]
  erw [DescendHom.pullSectionOn_naturality g' _ (ι ⁻¹ᵁ V), DescendHom.descendPsi_pull ι g' φ hinj t ht V hV s]
  rw [DescendHom.pullSectionOn_comp_hom, ht]

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericPullInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

lemma pullSectionOn_injective_of_basis_of_app (hPB : PullbackBasis.Statement.{0})
    {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules) {W : Z.Opens} {n : ℕ} {t : Fin n → Γ(M, W)}
    (ht : IsBasisOn M W t) (hg : Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M W) := by
  have hb := (hPB _ _ g M W n t ht).bijective_self
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => g.app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum g M W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hg (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]

lemma pullSectionOn_injective_of_app (hPB : PullbackBasis.Statement.{0}) {T Z : Scheme.{0}}
    (g : T ⟶ Z) (M : Z.Modules) (hM : IsVectorBundle M) (V : Z.Opens)
    (hg : ∀ W : Z.Opens, W ≤ V → Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M V) := by
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  apply modules_eq_of_locally M τ 0
  intro x hx
  obtain ⟨U, -, hxU, n, t, ht⟩ := hM x
  refine ⟨U ⊓ V, inf_le_right, ⟨hxU, hx⟩, ?_⟩
  rw [map_zero]
  apply pullSectionOn_injective_of_basis_of_app hPB g M (ht.restrict inf_le_left)
    (hg _ inf_le_right)
  rw [pullSectionOn_res g M inf_le_right (homOfLE ((Opens.map g.base).monotone inf_le_right)) τ,
    hτ, map_zero, map_zero]

theorem GenericPullInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackBasis.Statement.{0}) : GenericPullInj.Statement := by
  intro X f _ _ a ha G hG
  obtain ⟨m, hm, hinj⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn V hV => ?_⟩
  have hk0 : (a : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hn.ne')
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ hk0
  have hle : invOpen f ((a : ℤ) * n) ≤ invOpen f a := invOpen_mul_le_left f a n
  have hcomp : toInvOpen f ℚ ((a : ℤ) * n) hk ≫ X.homOfLE hle =
      toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) :=
    toInvOpen_homOfLE _ _ _ _ hle
  apply pullSectionOn_injective_of_app h₂ _ G hG V
  intro W hW
  have hWr : W ≤ (X.homOfLE hle).opensRange := by
    rw [Scheme.opensRange_homOfLE]
    exact hW.trans hV
  have hiso : IsIso ((X.homOfLE hle).app W) := Scheme.Hom.isIso_app _ W hWr
  have hj : Function.Injective ((X.homOfLE hle).app W) :=
    (ConcreteCategory.bijective_of_isIso ((X.homOfLE hle).app W)).1
  have hq : Function.Injective ((toInvOpen f ℚ ((a : ℤ) * n) hk).app ((X.homOfLE hle) ⁻¹ᵁ W)) :=
    hinj _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _) _
  rw [← hcomp, Scheme.Hom.comp_app]
  intro x y hxy
  exact hj (hq hxy)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem HeightOneSections.proof (h₁ : GenericGermInjective.Statement) :
    HeightOneSections.Statement := by
  intro X _ _ hN E hE U hU v hv
  have inj := h₁ X E hE

  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : (x : X) ∈ V) (σ : Γ(E, V)),
      ∀ hη : genericPoint X ∈ V, E.presheaf.germ V _ hη σ = v := by
    rintro ⟨x, hx⟩
    obtain ⟨W, -, hxW, n, s, hs⟩ := hE x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ W ⊓ U from ⟨hxW, hx⟩)
    have hη := HeightOneSections.genericPoint_mem hxV
    obtain ⟨σ, hσ⟩ := HeightOneSections.exists_section_of_isBasisOn HeightOneIntersection.proof
      hN E hVa hη (hs.restrict (hVle.trans inf_le_left)) v
      (fun y hy hy1 => hv y (hVle hy).2 hy1)
    exact ⟨V, hVle.trans inf_le_right, hxV, σ, fun _ => hσ⟩
  choose V hVU hxV σ hσ using loc

  have hcomp : TopCat.Presheaf.IsCompatible E.presheaf V σ := by
    intro i j
    refine BundlesAgree.section_ext E inj fun hη => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hσ, hσ]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨E.presheaf, E.isSheaf⟩ V U
    (fun x => homOfLE (hVU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) σ hcomp
  refine ⟨t, ?_⟩
  let x : U := ⟨genericPoint X, hU⟩
  have hη := HeightOneSections.genericPoint_mem (hxV x)
  have hx : E.presheaf.map (homOfLE (hVU x)).op t = σ x := ht x
  rw [← hσ x hη, ← hx, TopCat.Presheaf.germ_res_apply]

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomInjLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomInjLoc.proof (h₁ : LocSectionsInj.Statement) : SpreadHomInjLoc.Statement := by
  intro X f _ _ p U F G _ hG
  obtain ⟨m, hm, hpm, H⟩ := h₁ X f p
  refine ⟨m, hm, hpm, fun n hn hmn hpn ψ₁ ψ₂ e => ?_⟩
  set V : X.Opens := U ⊓ invOpen f n
  have hinj : ∀ W : (V : Scheme.{0}).Opens,
      Function.Injective ((baseChangeMap f (ZLoc p) ∣_ V).app W) := by
    intro W
    rw [morphismRestrict_app]
    refine (ConcreteCategory.bijective_of_isIso
      ((baseChange f (ZLoc p)).presheaf.map
        (eqToHom (image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) V W)).op)).1.comp
      (H n (fun h => hpn (Int.natCast_dvd_natCast.mp h)) (Int.natCast_dvd_natCast.mpr hmn) _ ?_)
    exact (V.ι_image_le W).trans inf_le_right
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : V ≤ U))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine PullbackFaithful.proof _ _ _ hinj _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomLoc.proof (h₁ : DescendHom.Statement) (h₂ : PullInjLoc.Statement)
    (h₃ : SpreadHomSectionsLoc.Statement) : SpreadHomLoc.Statement := by
  intro X f _ _ p U F G hF hG φ
  obtain ⟨m₁, hm₁, hp₁, H₁⟩ := h₂ X f p U G hG
  obtain ⟨m₂, hm₂, hp₂, H₂⟩ := h₃ X f p U F G hF hG φ
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun h => ((Nat.Prime.dvd_mul p.2).1 h).elim hp₁ hp₂,
    fun n hn hmn hpn => ?_⟩
  have hle : U ⊓ invOpen f n ≤ U := inf_le_left
  have hunit : IsUnit (((n : ℤ) : ℤ) : ZLoc p) :=
    isUnit_intCast_zLoc p n (by exact_mod_cast hpn)
  have hrange : Set.range (baseChangeMap f (ZLoc p) ∣_ U) ⊆ Set.range (X.homOfLE hle) := by
    rintro _ ⟨y, rfl⟩
    have hy : ((baseChangeMap f (ZLoc p) ∣_ U) y).1 ∈ invOpen f n := by
      rw [morphismRestrict_base_coe]
      have := range_baseChangeMap_subset f (ZLoc p) n hunit ⟨y.1, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact ⟨⟨_, ((baseChangeMap f (ZLoc p) ∣_ U) y).2, hy⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have e₂ : IsOpenImmersion.lift (X.homOfLE hle) _ hrange ≫ X.homOfLE hle =
      baseChangeMap f (ZLoc p) ∣_ U := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ V : (U : Scheme.{0}).Opens, V ≤ (X.homOfLE hle).opensRange →
      V ≤ invOpen (U.ι ≫ f) n := by
    intro V hV x hx
    have := hV hx
    rw [Scheme.opensRange_homOfLE] at this
    exact this.2
  obtain ⟨ψ, hψ⟩ := h₁ _ _ _ (X.homOfLE hle) _ _ e₂ F G φ
    (fun V hV => H₁ n hn (dvd_of_mul_right_dvd hmn) hpn V (hR V hV))
    (fun V hV => H₂ n hn (dvd_of_mul_left_dvd hmn) hpn V (hR V hV))
  refine ⟨ψ, ?_⟩
  have eg : Scheme.homOfLE _ ((baseChangeMap f (ZLoc p)).preimage_mono hle) ≫
      IsOpenImmersion.lift (X.homOfLE hle) _ hrange =
      baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n) := by
    rw [← cancel_mono (X.homOfLE hle), Category.assoc, e₂,
      morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) _ U hle]
  rw [← hψ, pullbackHomAlong_trans e₂ (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) _ U hle).symm
    eg rfl]

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

theorem SpreadStep.proof (h₁ : SpreadIsoLoc.Statement) (h₂ : SpreadGlue.Statement) :
    SpreadStep.Statement := by
  intro X f _ _ p E W₁ W₂ ⟨E₁, hE₁, ⟨α₁⟩⟩ ⟨E₂, hE₂, ⟨α₂⟩⟩
  obtain ⟨m, -, hmp, ψ, hψ⟩ := h₁ X f p (W₁ ⊓ W₂) _ _
    (hE₁.pullback_of_isOpenImmersion _) (hE₂.pullback_of_isOpenImmersion _)
    (overlapIso f (ZLoc p) E α₁ α₂)
  have hV : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range (invOpen f m).ι :=
    range_baseChangeMap_subset f _ m (isUnit_intCast_zLoc p m (by exact_mod_cast hmp))
  refine ⟨(W₁ ⊔ W₂) ⊓ invOpen f m, ?_, h₂ X f (ZLoc p) E W₁ W₂ E₁ E₂ hE₁ hE₂ α₁ α₂ _ hV ψ hψ⟩
  intro y hy
  have hyV : (baseChangeMap f (ZLoc p)).base y ∈ invOpen f m := by
    have := hV ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  refine ⟨?_, hyV⟩
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr hy

end GroundTheory.Heights₂.Heights.Model
end

