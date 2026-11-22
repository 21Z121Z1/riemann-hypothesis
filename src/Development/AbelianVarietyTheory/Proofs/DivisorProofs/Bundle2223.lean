import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TrNum

section
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')

theorem img_mul (g h : N.Gt) : I.img (g * h) = I.img g * I.img h :=
  ((I.rel_iff _ _).1 ((I.rel_img g).mul (I.rel_img h))).symm

theorem img_pow (g : N.Gt) (n : ℕ) : I.img (g ^ n) = I.img g ^ n :=
  ((I.rel_iff _ _).1 ((I.rel_img g).pow n)).symm

theorem img_io (y : N.X) : I.img (N.io y) = N'.io (I.e y) :=
  ((I.rel_iff _ _).1 (I.rel_io y)).symm

def imgQ {k : ℕ} (p : N.QT k) : N'.QT k :=
  ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), I.img p.1.2), by
    have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
    change I.img p.1.2 ^ k = N'.io (I.e p.1.1.toAdd)
    rw [← img_pow, h, img_io]⟩

theorem imgQ_mul {k : ℕ} (p q : N.QT k) : imgQ I (p * q) = imgQ I p * imgQ I q :=
  Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add I.e p.1.1.toAdd q.1.1.toAdd)) (img_mul I p.1.2 q.1.2))

theorem qEq_imgQ (hi : Function.Injective I.img) {k : ℕ} (p q : N.QT k) :
    N'.QEq (imgQ I p) (imgQ I q) ↔ N.QEq p q := by
  constructor
  · rintro ⟨z, h1, h2⟩
    obtain ⟨z, rfl⟩ := I.e.surjective z
    refine ⟨z, I.e.injective ?_, hi ?_⟩
    · rw [map_add, map_nsmul]; exact h1
    · rw [img_mul, img_io]; exact h2
  · rintro ⟨z, h1, h2⟩
    refine ⟨I.e z, ?_, ?_⟩
    · change I.e q.1.1.toAdd = I.e p.1.1.toAdd + k • I.e z
      rw [h1, map_add, map_nsmul]
    · change I.img q.1.2 = I.img p.1.2 * N'.io (I.e z)
      rw [h2, img_mul, img_io]

theorem imgQ_surjective (hi : Function.Bijective I.img) {k : ℕ} : Function.Surjective (imgQ I (k := k)) := by
  intro p'
  obtain ⟨g, hg⟩ := hi.2 p'.1.2
  have h : p'.1.2 ^ k = N'.io p'.1.1.toAdd := p'.2
  refine ⟨⟨(Multiplicative.ofAdd (I.e.symm p'.1.1.toAdd), g), ?_⟩, Subtype.ext (Prod.ext ?_ hg)⟩
  · change g ^ k = N.io (I.e.symm p'.1.1.toAdd)
    apply hi.1
    rw [img_pow, img_io, hg, h, AddEquiv.apply_symm_apply]
  · change Multiplicative.ofAdd (I.e (I.e.symm p'.1.1.toAdd)) = p'.1.1
    rw [AddEquiv.apply_symm_apply]; rfl

def formImg {k : ℕ} (β : N.Form k) : N'.Form k where
  be := β.be.compl₁₂ I.e.symm.toIntLinearEquiv.toLinearMap I.e.symm.toIntLinearEquiv.toLinearMap
  symm y z := β.symm _ _
  pos y hy := β.pos (I.e.symm y) (fun h => hy (by simpa using congrArg I.e h))
  dvd y z := β.dvd _ _

end

variable {F F' : Type} [Field F] [Field F'] {e : F ≃+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom (e : F →+* F') N N')

theorem units_bij (e : F ≃+* F') : Function.Bijective (Units.map (e : F →+* F').toMonoidHom) :=
  (Units.mapEquiv e.toMulEquiv).bijective

theorem img_bijective (hφ : Function.Bijective I.φ) (hh : ∀ x, I.h x = 1) : Function.Bijective I.img := by
  have hu := units_bij e
  constructor
  · intro g g' h
    have a := I.rel_img g
    have b := I.rel_img g'
    rw [h] at a
    refine NumD.Gt.ext (hφ.1 (a.1.symm.trans b.1)) (funext fun χ => hu.1 ?_)
    have a2 := a.2 χ
    have b2 := b.2 χ
    simp only [hh, _root_.mul_one] at a2 b2
    exact a2.symm.trans b2
  · intro g'
    obtain ⟨b, hb⟩ := hφ.2 g'.b
    choose s hs using fun χ => hu.2 (g'.s (I.e χ))
    refine ⟨⟨b, s, fun χ χ' => hu.1 ?_⟩, ((I.rel_iff _ _).1 ⟨hb.symm, fun χ => ?_⟩).symm⟩
    · have a := I.θ_eq (N.c χ) (N.c χ') b
      simp only [hh, _root_.mul_one] at a
      rw [map_mul, map_mul, hs, hs, hs, ← a, ← I.c_eq, ← I.c_eq, hb, map_add]
      exact g'.mult _ _
    · simp only [hh, _root_.mul_one]
      exact (hs χ).symm

theorem transport : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  intro F F' _ _ e N N' I hφ hh hl
  have hi := img_bijective I hφ hh
  have hu := units_bij e
  refine ⟨fun k β => ⟨formImg I β, fun a b => ?_⟩, fun m g hm ζ q hq => ⟨fun a => imgQ I (q a), ?_, ?_⟩⟩
  · change β.be (I.e.symm (I.e a)) (I.e.symm (I.e b)) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    refine ⟨h1.map_of_injective hu.1, fun a b => ?_, fun a b h => h3 a b ((qEq_imgQ I hi.1 _ _).1 h), fun p => ?_,
      fun i j => ?_⟩
    · rw [← imgQ_mul]; exact (qEq_imgQ I hi.1 _ _).2 (h2 a b)
    · obtain ⟨p, rfl⟩ := imgQ_surjective I hi p
      obtain ⟨a, ha⟩ := h4 p
      exact ⟨a, (qEq_imgQ I hi.1 _ _).2 ha⟩
    · rw [I.wp_eq (q (Pi.single i 1)) (q (Pi.single j 1)) _ _ rfl (I.rel_img _) rfl (I.rel_img _), h5, map_zpow]
  · rintro a f f' ⟨h1, h2⟩ hf
    refine ⟨fun h' χ => ?_, fun α hα x => ?_⟩
    · obtain ⟨h, rfl⟩ := hi.2 h'
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      rw [I.evT_eq hm (q a) _ rfl (I.rel_img _) χ h _ (I.rel_img _), ← h1]
      have r := (I.rel_img h).2 ((q a).1.1.toAdd + m • χ)
      simp only [hh, _root_.mul_one] at r
      have t : (imgQ I (q a)).1.1.toAdd + m • I.e χ = I.e ((q a).1.1.toAdd + m • χ) := by
        rw [map_add, map_nsmul]; rfl
      rw [t, r, (I.rel_img h).1, hf, hl, hh]
      simp
    · obtain ⟨α, rfl⟩ := I.e.surjective α
      obtain ⟨x, rfl⟩ := hφ.2 x
      rw [hf, h2 α (fun χ h => hα (I.e χ) (by rw [h, map_add, map_nsmul]; rfl)), map_zero]

end GlobalTheory.MBLow.TrNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtVec

open ReciprocityTheory.ChartRestriction.G.DVR

section Local

variable {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_cpt (hM : M.IsLB) {φ : K → (Sp S ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp S ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) {J} (hJ : Good M (cpt S) J) (e : val t (𝟙 _) (cpt S) J = val t' (𝟙 _) (cpt S) J) :
    LB.Gen.Corr M _ _ _ _ t t' := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM hF t' ht'
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio hM rfl t u ht hu
  have h1 : Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ ρ = 1 :=
    mul_eq_right.1 ((hρ _ _ _ J hJ).symm.trans (e.trans (vu _ _ _ J hJ).symm))
  have h2 : ρ = 1 := by
    apply Units.ext
    obtain ⟨a, ha⟩ := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective ρ.val
    have h3 : toStkA (cpt S) a = toStkA (cpt S) 1 := by
      rw [map_one]
      refine Eq.trans ?_ (congrArg Units.val h1)
      rw [gm_val (𝟙 (Sp S)) (cpt S) ⊤ trivial, ← ha]
      rfl
    rw [← ha, toStkA_injective h3, map_one]; rfl
  refine corr_of_val hM fun y I hI => (hρ _ _ y I hI).trans ?_
  rw [h2, map_one, _root_.one_mul]
  exact vu _ _ y I hI

theorem exists_gen_cpt (hM : M.IsLB) (φ : K → (Sp S ⟶ X)) (ε : K → ℤ) {J} (hJ : Good M (cpt S) J)
    (u : ((Sp S).presheaf.stalk (cpt S))ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) (cpt S) J = u := by
  have all : ∀ w : Sp S, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_cpt (𝟙 (Sp S)) _).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) :=
    fun j w hw => ⟨hw, all w⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(Sp S, ⊤)ˣ, Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ c = u := by
    obtain ⟨U, hU, a, ha⟩ := (Sp S).presheaf.exists_germ_eq u.val
    obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) U).2 hU)
    have hb : (Sp S).basicOpen a = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) _).2
      (((Sp S).mem_basicOpen a _ hU).2 (ha ▸ u.isUnit)))
    have ha' : IsUnit a := (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      ((Sp S).mem_basicOpen a y hy).1 (hb.ge trivial)
    exact ⟨ha'.unit, Units.ext ((gm_val (𝟙 _) _ ⊤ trivial _).trans ha)⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) * res le_top c⟩
  have v : ∀ (w : Sp S) j, w ∈ LB.wchart M φ j → Geo.Tor.gm (𝟙 (Sp S)) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * Geo.Tor.gm (𝟙 (Sp S)) w ⊤ c := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      (gm_res _ w le_top h c))
  refine ⟨t, isGen_of_gm _ fun w j j' h h' => ?_, (v _ _ (all _)).trans ?_⟩
  · refine (v w j h).trans (Eq.trans ?_ (congrArg _ (v w j' h')).symm)
    rw [← trF_trans hM _ ε (𝟙 _) w h h' (all w), _root_.mul_assoc]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) _ (all _) (all _) (all _)), _root_.one_mul, hc]

end Local

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

open GlobalTheory.TorusModel

theorem exists_over {S : Type} [CommRing S] [IsLocalRing S] (f : Sp S ⟶ Sp R) (b : Over.mk f ⟶ D.P.A) :
    ∃ g : GtPt D (Over.mk f), g.b = b := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt S)
  have C : IsCub (th D (T := Over.mk f) (cpt S) J) := isCub_cubV D.cub hJ
  obtain ⟨v, m₀, m⟩ := exists_mult C (c := cP D (Over.mk f)) (cPoint_add D _) b
  choose s hs hv using fun χ => exists_gen_cpt D.P.isLB (DegPre.gtφT D (Over.mk f) b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_) (hs 0) (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
      ((hv 0).trans (m₀.trans (val_one _).symm)),
    fun χ χ' => corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAtT (T := Over.mk f) hJ _ _ _))).trans
        ((m χ χ').trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl⟩
  · refine (prod_pt b 0 h).trans ?_
    rw [cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_pt b _ h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt b χ h) (prod_pt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ => (val_corr hJ (h.2 χ) _).trans (val_corr hJ (h'.2 χ) _).symm

omit [IsDomain R] in
theorem red_comp : redE R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), (∀ b : epsR R ⟶ D.P.A, IsTangent b → ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = b) ∧ (∀ gm gm' : GtPt D (epsR R), ∃ gm'', GtPt.IsAdd gm gm' gm'' ∧ (GtTan gm → GtTan gm' → GtTan gm'')) ∧ (∀ (T T' : Over (Sp R)) (h : T' ⟶ T) (gm : GtPt D T), ∃ gm' : GtPt D T', GtPt.IsPull h.left gm gm') ∧ ∀ gm gm' : GtPt D (epsR R), gm.b = gm'.b → (∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (gm.s χ) (gm'.s χ)) → gm = gm' := by
  intro R _ _ _ D
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨G, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => isZero_of_isAdd (by simpa using ha T 1 1)
  let r : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) red_comp
  let a : epsR R ⟶ baseOver (Sp R) := Over.homMk (spMap (algebraMap R (DualNumber R))) (Category.comp_id _)
  have hra : r ≫ a = 𝟙 _ := Over.OverMorphism.ext red_comp
  have tan : ∀ x : epsR R ⟶ G, GtTan (Φ _ x) ↔ r ≫ x = 1 := fun x =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hp _ _ r x) h).trans (isZero_unique ho (hz _))),
      fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ r x⟩⟩
  refine ⟨fun b hb => ?_, fun g g' => ?_, fun T T' h g => ?_, fun g g' hb hs =>
    pt_ext hb fun χ _ _ hJ => val_corr hJ (hs χ) _⟩
  · have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
      simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
        IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
    obtain ⟨g, hg⟩ := exists_over (D := D) _ b
    obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    refine ⟨Φ _ (((a ≫ r) ≫ x)⁻¹ * x), (tan _).2 ?_, ?_⟩
    · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, hra, Category.id_comp,
        inv_mul_cancel]
    · have h₁ := ((TorusModel.isAdd_iff _ _ _).1 (ha _ ((a ≫ r) ≫ x) (((a ≫ r) ≫ x)⁻¹ * x))).1
      have h₂ := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ (a ≫ r) x)).1
      have h₃ : r ≫ b = 1 := Over.OverMorphism.ext (hb.trans (Category.id_comp _).symm)
      rw [mul_inv_cancel_left, h₂, hg, Category.assoc, h₃, MonObj.comp_one, _root_.one_mul] at h₁
      exact h₁.symm
  · obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    obtain ⟨x', rfl⟩ := (Φ (epsR R)).surjective g'
    refine ⟨_, ha _ x x', fun h h' => (tan _).2 ?_⟩
    rw [MonObj.comp_mul, (tan _).1 h, (tan _).1 h', _root_.mul_one]
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    exact ⟨_, hp _ _ h x⟩

end GlobalTheory.MBLow.GtVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section General

variable {R : Type} [CommRing R] (I : Ideal R)

theorem dualMap_mk_struct (e : ℕ) :
    spMap (algebraMap (R ⧸ I ^ (e + 1)) (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsR R).hom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => ?_)
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_factor_dualMap (e : ℕ) :
    ∃ l, l ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      adicLevelι (I.map (algebraMap R (DualNumber R))) (e + 1) := by
  have hs : Function.Surjective (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) := fun x => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective x.snd
    refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [dualMap, ha, hb]
  have hk : RingHom.ker (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≤
      RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap R (DualNumber R))) ^ (e + 1))) := fun x hx => by
    rw [RingHom.mem_ker] at hx
    have h1 : x.fst ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.fst hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have h2 : x.snd ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.snd hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have ex : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [Ideal.mk_ker, ← Ideal.map_pow, ex]
    exact add_mem (Ideal.mem_map_of_mem _ h1) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))
  refine ⟨spMap (RingHom.liftOfSurjective _ hs ⟨_, hk⟩), ?_⟩
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]

variable {I} [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_iff_isPointOf (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) :
    TanRel U y gm ↔ FormalPoint.IsPointOf U gm y := by
  constructor
  · intro h
    refine (FormalPoint.isPointOf_iff_reduction U gm y).2 fun e => ?_
    obtain ⟨ye, h1, h2⟩ := h e
    obtain ⟨l, hl⟩ := exists_factor_dualMap I e
    have h3 : FormalPoint.HasCoords U e gm _ ye := h2
    have h4 := h3.comp l
    have h5 : FormalPoint.reduction I y e = l ≫ ye := by
      rw [← cancel_mono (fstG I e G).left, FormalPoint.reduction_fstG, Category.assoc, h1, ← hl]
      exact Category.assoc _ _ _
    rw [h5, ← hl]
    exact h4
  · intro h e
    obtain ⟨ye, hy⟩ := FormalPoint.exists_hasCoords U e gm _ _ (dualMap_mk_struct I e)
    exact ⟨ye, h.comp_fstG_eq hy, hy⟩

theorem isTangent_of_isPointOf [IsLocalRing R] [IsAdicComplete I R] {y : epsR R ⟶ G} {gm : GtPt D.toPre (epsR R)}
    (hg : GtTan gm) (h : FormalPoint.IsPointOf U gm y) : IsTangent y := by
  obtain ⟨o, ho, hp⟩ := hg
  let k : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
      RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
    rw [h3]
    exact Spec.map_id _)
  have h1 : k ≫ y = 1 := (FormalPoint.existsUnique_isPointOf_unit U o).unique (h.pull k hp)
    (FormalPoint.isPointOf_one U ho)
  refine (congrArg (·.left) h1).trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end General

theorem existsUnique_tangent_of_gtTan : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ gm : GtPt D.toPre (epsR V), GtTan gm → ∃! y : epsR V ⟶ G, IsTangent y ∧ TanRel U.toUnifPre y gm := by
  intro V _ _ _ _ hV D A G _ _ _ U gm hg
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have : Nontrivial (DualNumber V) := (TrivSqZeroExt.inl_injective (R := V) (M := V)).nontrivial
  have : IsLocalRing (DualNumber V) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  obtain ⟨y, hy, hu⟩ := FormalPoint.existsUnique_isPointOf U.toUnifPre gm
  exact ⟨y, ⟨isTangent_of_isPointOf _ hg hy, (tanRel_iff_isPointOf _ _ _).2 hy⟩,
    fun y' h' => hu y' ((tanRel_iff_isPointOf _ _ _).1 h'.2)⟩

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.DiscNorm

theorem norm_eq_zpow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {C : Type} [NormedField C] (f : FractionRing V →+* C) (hf : ∀ r : V, ‖f (algebraMap V _ r)‖ ≤ 1)
    {k : FractionRing V} (hk : k ≠ 0) : ∃ n : ℤ, ‖f k‖ = ‖f (algebraMap V _ ϖ)‖ ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hk
  set g : V →+* C := f.comp (algebraMap V _)
  have key : ∀ x : V, x ≠ 0 → ∃ m : ℕ, ‖g x‖ = ‖g ϖ‖ ^ m := fun x hx => by
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    refine ⟨m, ?_⟩
    rw [map_mul, norm_mul, map_pow, norm_pow, GlobalTheory.Ex.IntVal.norm_unit g hf u.isUnit, _root_.one_mul]
  obtain ⟨ma, ea⟩ := key a ha0
  obtain ⟨mb, eb⟩ := key b hb0
  have ht : ‖g ϖ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) (f.injective (by simpa [g] using h)))
  refine ⟨(ma : ℤ) - mb, ?_⟩
  show ‖f (algebraMap V _ a / algebraMap V _ b)‖ = ‖g ϖ‖ ^ ((ma : ℤ) - mb)
  rw [map_div₀, norm_div]
  show ‖g a‖ / ‖g b‖ = _
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast]
  exact congrArg₂ (· / ·) ea eb

theorem vF_eq_alg {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (J : (Sp F ⟶ X) → L.ι)
    (hW : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))) :
    ∃ k : FractionRing R, k ≠ 0 ∧ vF t (jFK (R := R) F) J = algebraMap (FractionRing R) F k := by
  set W := LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))
  have h' : ⊤ ≤ (𝟙 (TK R).left) ⁻¹ᵁ W := by
    intro x _
    obtain ⟨y⟩ : Nonempty (Sp F) := inferInstance
    have hy := hW (Set.mem_univ y)
    have hs : Subsingleton (PrimeSpectrum (FractionRing R)) := inferInstance
    have : (jFK (R := R) F).base y = x := @Subsingleton.elim (PrimeSpectrum (FractionRing R)) hs _ _
    rw [← this]; exact hy
  refine ⟨GlobalTheory.Ex.IntVal.evR (𝟙 _) W h' (t.s _).val, ?_, ?_⟩
  · exact ((Units.isUnit _).map _).ne_zero
  · have := GlobalTheory.Ex.IntVal.valF_comp (algebraMap (FractionRing R) F) (𝟙 (TK R).left) W h' (t.s _).val
    have e : spMap (algebraMap (FractionRing R) F) ≫ 𝟙 (TK R).left = jFK (R := R) F := Category.comp_id _
    rw [e] at this
    exact this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  intro V _ _ _ ϖ hϖ D C _ _ _ hC N ν hν
  obtain ⟨S, hS, hI⟩ := hν
  let f : V →+* C := toF V C
  let g : V →+* S := f.codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hrig : ‖ν.rg‖ = 1 := GlobalTheory.Ex.IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w η[D.toPre.P.A])).trans (Category.comp_id _)
  refine ⟨hrig, fun χ => ?_⟩
  have hW : ⊤ ≤ jFK (R := V) C ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => D.toPre.xK (ν.eX χ))
      (fun _ => ν.J (jFK (R := V) C ≫ D.toPre.xK (ν.eX χ))) := fun y hy => Set.mem_iInter.2 fun _ => ν.good _ hy
  obtain ⟨k, hk, ek⟩ := vF_eq_alg (D.toPre.psi (ν.eX χ)) ν.J hW
  obtain ⟨n, hn⟩ := norm_eq_zpow hϖ (algebraMap (FractionRing V) C) hC.1 hk
  refine ⟨n, ?_⟩
  rw [ν.ψ_eq, norm_mul]
  change _ * ‖ν.rg‖ = _
  rw [hrig, _root_.mul_one, ek, hn]
  rfl

end GlobalTheory.MBLow.DiscNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerPreservesSchwartzSpaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_preserves_schwartz_space : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  first | exact @GlobalTheory.ModelTr.exists_isWeil_trans | exact GlobalTheory.ModelTr.exists_isWeil_trans | (intros; apply GlobalTheory.ModelTr.exists_isWeil_trans <;> assumption)
end

