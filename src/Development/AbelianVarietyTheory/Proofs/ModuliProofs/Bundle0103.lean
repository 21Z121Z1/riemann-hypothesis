import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem sym_inv_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁, Hom.inv_def] at e
  refine e.trans ?_
  show ((𝟙 G' : G' ⟶ G').left ≫ φ) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_of_cover (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A]
    (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (hU : iSup U = ⊤)
    (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (L : LB A.left) (M : ∀ i, LB (G i).left) (hL : L.IsLB)
    (hM : ∀ i, (M i).IsLB) (hw : ∀ i, LBIso (M i) (L.pull (ψ i))) (hs : ∀ i, Out.Sym (G i) (M i)) :
    Out.Sym A L := by
  intro s
  obtain ⟨i, hi⟩ : ∃ i, s ∈ U i := TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial)
  obtain ⟨V, hV, c, hc⟩ := hs i ⟨s, hi⟩
  obtain ⟨w, hw⟩ := hw i
  refine ⟨(U i).ι ''ᵁ V, ⟨⟨s, hi⟩, hV, rfl⟩, ?_⟩
  have hp := (hψ i).1

  obtain ⟨b, hb⟩ : ∃ b : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ V.toScheme,
      b ≫ V.ι ≫ (U i).ι = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom :=
    ⟨IsOpenImmersion.lift (V.ι ≫ (U i).ι) _ (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz, e⟩ := y.2
      exact ⟨⟨z, hz⟩, e⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom = (b ≫ V.ι) ≫ (U i).ι := by rw [Category.assoc, hb]
  let m := hp.lift _ _ sq
  have m₁ : m ≫ ψ i = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι := hp.lift_fst _ _ _
  have m₂ : m ≫ (G i).hom = b ≫ V.ι := hp.lift_snd _ _ _
  obtain ⟨n, hn⟩ : ∃ n : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ ((G i).hom ⁻¹ᵁ V).toScheme,
      n ≫ ((G i).hom ⁻¹ᵁ V).ι = m :=
    ⟨IsOpenImmersion.lift _ m (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ V) m₂).mpr (b y).2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL (hM i) c hc
  refine gen_chartPull (chartPullSame L _ _ _ n fun k => ?_) c₂ h₂
  fin_cases k
  · show _ ≫ _ = n ≫ (_ ≫ _) ≫ ψ i
    rw [Category.assoc, sym_inv_comm (hψ i), ← Category.assoc n, hn, ← Category.assoc m, m₁]
  · show (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι = n ≫ ((G i).hom ⁻¹ᵁ V).ι ≫ ψ i
    rw [← Category.assoc n, hn, m₁]

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsoIffAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PelUnifCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped CategoryTheory.Obj

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (hs : Function.Surjective (G3 G).hom.appTop.hom) {M : RigLB G} (c c' : CubicalStr G M) : c = c' := by
  have h : LB.Gen.Corr M.L _ _ _ _ c.t c'.t :=
    AbLaw.Cube.corr_of_val_section M.isLB hs (lift 1 (lift 1 1))
      (φ := thφ G (x3 G)) (ε := thε) (φ' := thφ G (x3 G)) (ε' := thε) (fun _ _ _ => rfl) c.isGen c'.isGen
      fun _ _ hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm
  have e : c.t = c'.t := TorusExt.gen_ext_val M.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen
    fun _ _ hJ => val_corr hJ h _
  cases c
  cases c'
  cases e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem cubG_heq (P : PELUnif I t) : HEq P.U.cubG t.cub := by
  have := P.U.smooth
  have hs := SymExtend.surjective_cube_of_generic GlobalTheory.globalFns_holds t.G P.A.isAb P.U.gen
  have key : ∀ (M : RigLB t.G) (c : CubicalStr t.G M), M = t.PP → HEq c t.cub := by
    rintro M c rfl
    exact heq_of_eq (cubical_eq hs c t.cub)
  exact key _ _ P.bundle

def pelEquiv (I : Ideal R) (t : SAB H (Sp R)) : PELUnif I t ≃ UniformTorsionIsomorphism.PELUnif I t where
  toFun P :=
    { dat := { D := P.D, mod := P.mod, ac := P.oD, through := (DegActCompare.psiW0_host_iff H P.oD).1 P.w0 }
      unif := { A := P.A, actA := P.oA, U := P.U, LG_eq := P.bundle, cub_eq := cubG_heq P, lin := P.lin } }
  invFun Q :=
    { D := Q.dat.D, mod := Q.dat.mod, oD := Q.dat.ac, A := Q.unif.A, oA := Q.unif.actA, U := Q.unif.U
      bundle := Q.unif.LG_eq, lin := Q.unif.lin
      w0 := (DegActCompare.psiW0_host_iff H Q.dat.ac).2 Q.dat.through }
  left_inv _ := rfl
  right_inv _ := rfl

variable (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev genMap : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)

theorem genMap_cart : IsGrpPullback P.A.A t.G (jK R) (genMap P) := by
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl

abbrev pt (x : TF (R := R) F ⟶ t.G) : TFK (R := R) F ⟶ P.A.A := (pelEquiv I t P).unif.ptA F x

theorem pt_left (x : TF (R := R) F ⟶ t.G) : (pt P F x).left ≫ genMap P = x.left := by
  have hi : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show ((UniformTorsionIsomorphism.toGen x).left ≫ P.U.gen.hom.left) ≫ P.U.gen.inv.left ≫ _ = _
  rw [Category.assoc, ← Category.assoc P.U.gen.hom.left, hi, Category.id_comp]
  exact UniformTorsionIsomorphism.toGen_fst x

theorem ext_genMap {x y : TFK (R := R) F ⟶ P.A.A} (h : x.left ≫ genMap P = y.left ≫ genMap P) : x = y :=
  Over.OverMorphism.ext ((genMap_cart P).1.hom_ext h (by rw [Over.w x, Over.w y]))

def ptEquiv : (TF (R := R) F ⟶ t.G) ≃* (TFK (R := R) F ⟶ P.A.A) :=
  MulEquiv.symm
    { pushHom (genMap_cart P) (TFK (R := R) F) with
      invFun := pt P F
      left_inv := fun _ => ext_genMap P F (pt_left P F _)
      right_inv := fun x => Over.OverMorphism.ext (pt_left P F x) }

def TorsionIsoAt (k : ℕ) : Prop :=
  letI := H.starRing
  ∃ f : QkPt P.D.toPre F k → (TFK (R := R) F ⟶ P.A.A),
    (∀ p x, P.ToA F k p x ↔ x = f p) ∧ (∀ x, x ^ k = 1 → ∃ p, f p = x) ∧
    (∀ p p', f p = f p' ↔ QkPt.Equiv P.D.toPre F p p') ∧
    (∀ p p' p'', Geo.Tor.QkAdd p p' p'' → f p'' = f p * f p') ∧
    (∀ a p p', QkAct P.oD a p p' → f p' = f p ≫ P.oA.act a) ∧
    ∀ p p' (z : Fˣ), WeilQkIs P.D.toPre F k p p' z ↔ WeilIs P.A.A P.A.L k (f p) (f p') (unitOn z)

end GlobalTheory.PelUnifCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.WeilFieldExt

open GlobalTheory.CommPairing ReciprocityTheory.ChartRestriction.G.Out

theorem corr_of_val_epi {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Y' ⟶ Y) [Epi q]
    (hq : ∀ U : Y.Opens, Function.Injective (q.app U).hom)
    (h : ∀ y J, Good L y J → val t q y J = val t' q y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have inj : Function.Injective (pullU q (LB.wchart L φ j ⊓ LB.wchart L φ' j')) := fun a b e =>
    Units.ext (hq _ (congrArg Units.val e))
  apply inj
  refine unit_ext fun y hy => ?_
  have hy' : q y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun k => q ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    intro a b e
    have e := (cancel_epi q).1 e
    rcases a with a | a <;> rcases b with b | b
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy'.1 a, Set.mem_iInter.1 hy'.2 a])
  have := h y J hJ
  rw [val_of t _ y J j (fun k => e (.inl k)), val_of t' _ y J j' (fun k => e (.inr k))] at this
  exact (gm_id_pull q y _ hy' _).trans ((gm_res _ y _ hy' _).trans (this.trans
    ((gm_res _ y _ hy' _).symm.trans (gm_id_pull q y _ hy' _).symm)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine (IsPullback.of_right (h₁₁ := (h ▷ A).left) (v₁₁ := pullback.fst T'.hom A.hom)
    (h₁₂ := pullback.snd T.hom A.hom) (v₁₂ := pullback.fst T.hom A.hom) (h₂₁ := h.left) (h₂₂ := T.hom)
    (v₁₃ := A.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom A.hom).flip)
  · have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
      congrArg (fun q => q.left) (whiskerRight_snd h A)
    rw [e, Over.w h]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · exact congrArg (fun q => q.left) (whiskerRight_fst h A)

theorem commIsOf_descend (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    [Epi (h ▷ A).left] (hq : ∀ U, Function.Injective ((h ▷ A).left.app U).hom)
    {θx θy : ThetaGrp A L k T} {a b : ThetaGrp A L k T'} (ha : a.pt = h ≫ θx.pt) (hb : b.pt = h ≫ θy.pt)
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k a b (Units.map h.left.appTop.hom.toMonoidHom c)) :
    CommIsOf A L k θx θy c := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1
    (commIsOf_change globalFns_holds hA hL (hx.trans ha.symm) (hy.trans hb.symm) H)
  refine corr_of_val_epi hL (h ▷ A).left hq fun z J hJ => ?_
  have key : ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (h ▷ A).left z J =
        tval θ (h ▷ A).left z J * tval θ' ((h ▷ A).left ≫ (translT A θ.pt).left) z J := fun θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ (h ▷ A).left z J * ·) (val_pull hJ _ _ _))
  have e := H' _ (𝟙 _) z J hJ
  have t : ∀ x : T ⟶ A, (𝟙 _ ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (h ▷ A).left ≫ (translT A x).left := fun x => by
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (𝟙 _ ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((h ▷ A).left ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (𝟙 _ ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g, Category.id_comp] at e
  exact (key θx θy).trans (e.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key θy θx) (H1.val_constGen L c _ z J))).symm)

theorem weilIs_iff (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} [Unique T.left] (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k x y c ↔
      ∃ θx θy : ThetaGrp A L k T, θx.pt = x ∧ θy.pt = y ∧ CommIsOf A L k θx θy c := by
  constructor
  · intro H
    obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H default
    obtain rfl : V = ⊤ := eq_top_iff.2 fun p _ => by rwa [Unique.eq_default p]
    let s : T ⟶ overRes (⊤ : T.left.Opens) := Over.homMk T.left.topIso.inv (by
      show T.left.topIso.inv ≫ T.left.topIso.hom ≫ T.hom = T.hom
      rw [Iso.inv_hom_id_assoc])
    have w : s.left ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.topIso.inv_hom_id
    have w' : s ≫ overResι ⊤ = 𝟙 T := Over.OverMorphism.ext w
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL s (hc θx θy hx hy)
    rw [hx, ← Category.assoc, w', Category.id_comp] at ha
    rw [hy, ← Category.assoc, w', Category.id_comp] at hb
    have e : Units.map s.left.appTop.hom.toMonoidHom (unitRes ⊤ c) = c := by
      apply Units.ext
      have := congrArg (fun q => q.appTop.hom c.val) w
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this
    rw [e] at H'
    exact ⟨a, b, ha, hb, H'⟩
  · rintro ⟨θx, θy, rfl, rfl, H⟩ p
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
    exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
      commIsOf_change globalFns_holds hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem exists_lift_descend (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    (hd : ∀ M : LB (T ⊗ A).left, M.IsLB → (∃ t : (M.pull (h ▷ A).left).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (x : T ⟶ A) (a : ThetaGrp A L k T') (ha : a.pt = h ≫ x) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨t, ht⟩ := hd (thetaLB A L k x) (DVR.linComb_isLB L hL _ _)
    (gen_chartPull (chartPullOut L ![(snd T A).left, (translPt A x).left] ![k, -k] (h ▷ A).left
      ![(snd T' A).left, (translPt A a.pt).left] (fun i => by
        fin_cases i
        · exact (congrArg (fun q => q.left) (whiskerRight_snd h A)).symm
        · show (translPt A a.pt).left = (h ▷ A).left ≫ (translPt A x).left
          rw [← Over.comp_left, whisker_translPt, ha])) a.φ a.isGen)
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

end GlobalTheory.WeilFieldExt

namespace GlobalTheory

open WeilFieldExt CommPairing in

theorem weilIs_fieldExt_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  intro S G _ K Ω _ _ i x L k y y' c hG hL
  rw [unitOn_map]
  let h : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  refine ⟨fun H => ?_, fun H => weilIs_pull globalFns_holds hG hL h H⟩
  letI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum K))
  letI : Unique (Over.mk (spMap i ≫ x)).left := inferInstanceAs (Unique (PrimeSpectrum Ω))
  obtain ⟨a, b, ha, hb, Hc⟩ := (weilIs_iff hG hL _ _ _).1 H
  have pb : IsPullback (h ▷ G).left (fst _ G).left (fst _ G).left (spMap i) := isPullback_whisker h
  obtain ⟨e, -, -, -, inj⟩ := (FieldBaseChange.epi_and_isMonHom_iff K Ω i).1 _ _ _ _ _ pb
  have hd := (GlobalTheory.T.lineBundle_trivial_iso_descend_field K Ω i _ _ _ _ _
    (by have := hG.smooth; exact inferInstanceAs (Smooth (pullback.fst x G.hom)))
    (by have := hG.proper; exact inferInstanceAs (IsProper (pullback.fst x G.hom)))
    (by have := hG.geomConnected; exact inferInstanceAs (GeometricallyConnected (pullback.fst x G.hom))) pb).1
  obtain ⟨θ, rfl⟩ := exists_lift_descend hL h hd y a ha
  obtain ⟨θ', rfl⟩ := exists_lift_descend hL h hd y' b hb
  exact (weilIs_iff hG hL _ _ _).2 ⟨θ, θ', rfl, rfl, commIsOf_descend hG hL h inj ha hb Hc⟩

end GlobalTheory
end
end

