import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.RaisedAmple

theorem exists_closure {O F F' : Type} [CommRing O] [Field F] [Field F'] [CharZero F] [CharZero F'] (β : O →+* F)
    (k : F →+* F') (hβ : IsDedFrac β) (hk : k.Finite) :
    ∃ (O' : Type) (_ : CommRing O') (β' : O' →+* F') (b : O →+* O'), IsDedFrac β' ∧ β'.comp b = k.comp β ∧ b.Finite ∧
      ∀ x : F', IsIntegral ℤ x → x ∈ β'.range := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := k.toAlgebra
  letI := (k.comp β).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F F' := hk
  have hD : IsDedekindDomain (integralClosure O F') := integralClosure.isDedekindDomain O F F'
  have hF : IsFractionRing (integralClosure O F') F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hfin : Module.Finite O (integralClosure O F') := IsIntegralClosure.finite O F F' _
  refine ⟨integralClosure O F', inferInstance, algebraMap _ F', algebraMap O _, ⟨⟨inferInstance, hD⟩, inferInstance, hF⟩,
    rfl, hfin, fun x hx => ⟨⟨x, hx.tower_top⟩, rfl⟩⟩

theorem lift_lift {T X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (k : W ⟶ Z) (hk : g' ≫ g = k) (r : T ⟶ X)
    (s : T ⟶ W) (w : r ≫ f = s ≫ k) (r' : T ⟶ pullback f g) (h₁ : r' ≫ pullback.fst _ _ = r)
    (h₂ : r' ≫ pullback.snd _ _ = s ≫ g') :
    ∃ e : pullback f k ≅ pullback (pullback.snd f g) g', pullback.lift r' s h₂ = pullback.lift r s w ≫ e.hom := by
  subst hk
  refine ⟨(pullbackLeftPullbackSndIso f g g').symm, ?_⟩
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst, h₁]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.lift_snd]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isIntegral_zeta {A : ℕ} (hA : 0 < A) : IsIntegral ℤ (zeta A) :=
  (Complex.isPrimitiveRoot_exp A hA.ne').isIntegral hA

theorem exists_coeff {l : Level H} (c : Coeff l) (l' : Level H) : ∃ c' : Coeff l', c.F ≤ c'.F := by
  have := c.fin
  have := GlobalTheory.BaseRing.finiteDimensional_KA l'
  have hM : 0 < l'.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l'.three_le) l'.A_pos
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l'.M'}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_zeta hM).tower_top
  refine ⟨⟨(c.F ⊔ KA l') ⊔ IntermediateField.adjoin ℚ {zeta l'.M'}, inferInstance, fun τ a => ?_, ?_, ?_⟩, ?_⟩
  · exact (le_sup_left.trans le_sup_left : c.F ≤ _) (c.conj τ a)
  · exact (le_sup_right : IntermediateField.adjoin ℚ {zeta l'.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_left.trans le_sup_left

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← Nat.div_mul_div hd'.1 hd.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc,
      h.1, Category.assoc]
  · rw [← Nat.div_mul_div hd'.2.2 hd.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a),
      Category.assoc, h.2, Category.assoc]

theorem exists_isInc_of_mem {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S A : ℕ}
    (h₁ : (1 + H.rt0) / 2 ∈ i.range) (h₂ : (S : ℂ)⁻¹ ∈ i.range) (h₃ : zeta A ∈ i.range) :
    ∃ b : RZ H S A →+* O, IsInc (RZ H S A).subtype i b := by
  have hle : RZ H S A ≤ i.range := by
    unfold RZ
    rw [Subring.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))

theorem exists_cover (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O]
    [CommRing O'] {β : O →+* c.F} {β' : O' →+* c'.F} (Y : Model (Xo l) c β) (b : O →+* O') (d : l.Dvd l')
    (hc : c.F ≤ c'.F) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = (IntermediateField.inclusion hc).toRingHom.comp β) (hfin : b.Finite) :
    ∃ (Y' : Model (Xo l') c' β') (r : (Xo l').XF c' ⟶ (Xo l).XF c) (ν : SABMap Y'.oF.t Y.oF.t r)
      (a : (ofModel Y').Above (ofModel Y) b r ν), LevComp Y'.oF Y.oF r ν ∧ IsFinite a.π ∧ Surjective a.π := by
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l' (KA l') (KA l') (baseKA l') (baseKA l') (RingHom.id _) _ _ (Xo l').s
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ (Xo l').s)
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l').univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -, hs⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l' c' o m0 d
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l').XF c' ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp o Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩
  obtain ⟨e, he⟩ := lift_lift (Xo l).s _ _ (spMap k) (by rw [hkk, spMap_comp]) r _ hr r' hr₁ hr₂
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hs' : Surjective (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hsm : Smooth (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) := by
    have := (Xo l').smooth
    have : Smooth (Xo l').s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, ⟨a⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ Y.oF.t β _ _ _
    (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) o.t β' (ofModel Y) b _ r' hr₂ ν' hβ hβ'
    hb hnorm hf'
  have hπ : IsFinite a.π := by
    have := a.fin
    have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hfin
    rw [← pullback.lift_fst a.π C.s a.π_over]
    infer_instance
  have hr' : Surjective r' := by
    have : Surjective (spMap (IntermediateField.inclusion hc).toRingHom) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    rw [← pullback.lift_fst r' _ hr₂]
    infer_instance
  have hj : IsDominant (ofModel Y).j := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.2.2.2.2.1
  have hd : IsDominant a.π := by
    have : IsDominant (C.j ≫ a.π) := by rw [a.j_comm]; infer_instance
    exact IsDominant.of_comp C.j a.π
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    r', ν', a, hl', hπ, surjective_of_isDominant_of_isClosed_range a.π a.π.isClosedMap.isClosed_range⟩

theorem amp_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨n ^ k, Y'.X, a.π, Y'.t, a.mu, hodd.pow, by rw [Nat.cast_pow]; exact hu.pow k, hf, hs, ⟨A'⟩⟩

end GlobalTheory.RaisedAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelData_pullback_of_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  first | exact @GlobalTheory.SiegelDataPull.siegData_pull | exact GlobalTheory.SiegelDataPull.siegData_pull | (intros; apply GlobalTheory.SiegelDataPull.siegData_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegDesc

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem spMap_subtype_inclusion {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem siegPre_descends : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  intro h M o _ ζ K _ K₀ s₀ s c hs hc
  classical
  obtain ⟨sA, hA⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)
  let K' : Subfield K := K₀ ⊔ Subfield.closure (sA : Set K)
  obtain ⟨X', p', φ', hproj, hpb⟩ := hA K' le_sup_left
    (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))
  have : IsProper p' := by
    obtain ⟨N, i, _, rfl⟩ := hproj
    have := isProper_str K' N
    infer_instance
  have : LocallyOfFinitePresentation p' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let A' : Over (Sp K') := Over.mk p'
  have : IsProper A'.hom := ‹IsProper p'›
  have : LocallyOfFinitePresentation A'.hom := ‹LocallyOfFinitePresentation p'›
  have hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype) := hpb
  obtain ⟨sG, hG⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'
  obtain ⟨φ₂', hsq'⟩ := exists_isSquare hpb'.w
  have : IsProper (A' ⊗ A').hom := by
    change IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)
    infer_instance
  obtain ⟨sL, hL⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂'
    c.P c.isLB (isPullback_of_isSquare hpb' hsq')
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left :=
    ⟨_, fun _ => rfl⟩
  have hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K) := fun u =>
    (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))
  obtain ⟨sP, hP⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h)
    (fun u => lv u ≫ φ') IsPullback.of_id_snd
    (fun u => by
      have e := hlev u
      rw [Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])
  refine ⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩ := hF
  have h' : K' ≤ K₁ := sup_le hK (Subfield.closure_le.2 hsA)
  let j := spMap (Subfield.inclusion h')
  have hj : spMap K₁.subtype ≫ j = spMap K'.subtype := spMap_subtype_inclusion h'
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p' j)
  let φ₁ : A₁.left ⟶ A'.left := pullback.fst p' j
  have hpb₁ : IsPullback φ₁ A₁.hom A'.hom j := IsPullback.of_hasPullback p' j
  let ψ : c.A.left ⟶ A₁.left := hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, hj]; exact hpb.w)
  have hψ₁ : ψ ≫ φ₁ = φ' := hpb₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype := hpb₁.lift_snd _ _ _
  obtain ⟨grp, hgrp⟩ := hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂
  obtain ⟨φ₂, hsq₁⟩ := exists_isSquare hpb₁.w
  obtain ⟨ψ₂, hsqψ⟩ := exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂
    (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)
  obtain ⟨f₁, hf₁⟩ := hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left) := fun u => hpb₁.lift (f₁ u) (𝟙 _)
    (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))
  have hl₁ : ∀ u, l u ≫ φ₁ = f₁ u := fun u => hpb₁.lift_fst _ _ _
  have hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _ := fun u => hpb₁.lift_snd _ _ _
  let lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun u => Over.homMk (l u) (hl₂ u)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_siegelObject_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁
    lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by
      have e := hlev u
      have key : lv u ≫ ψ = spMap K₁.subtype ≫ l u := by
        apply hpb₁.hom_ext
        · rw [Category.assoc, Category.assoc, hψ₁, hl₁]
          exact (hf₁ u).1.symm
        · rw [Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]
      exact (congrArg (· ≫ ψ) (hlv u)).symm.trans key)
  exact ⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩

end GlobalTheory.SiegDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureComponentTrdegGeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaClosure_component_trdeg_ge : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  first | exact @GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent | exact GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent | (intros; apply GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectConstantFamilyDualNumbersIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  first | exact @GlobalTheory.KS.tMap_of_isConst | exact GlobalTheory.KS.tMap_of_isConst | (intros; apply GlobalTheory.KS.tMap_of_isConst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSections_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  first | exact @GlobalTheory.embSec_veryAmple_periodic | exact GlobalTheory.embSec_veryAmple_periodic | (intros; apply GlobalTheory.embSec_veryAmple_periodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLevel_extends_from_dense_open_normal : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  first | exact @GlobalTheory.exists_torsion_level_extend | exact GlobalTheory.exists_torsion_level_extend | (intros; apply GlobalTheory.exists_torsion_level_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuativeLiftGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_lift_generic_point : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X Y : Scheme.{0}) (f : X ⟶ Y) (sY : Y ⟶ Sp O), IsQProjOver (f ≫ sY) → IsSeparated sY → LocallyOfFiniteType sY → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.ValuativeGeneric.isProper_of_lift_generic_of_finiteType | exact GlobalTheory.ValuativeGeneric.isProper_of_lift_generic_of_finiteType | (intros; apply GlobalTheory.ValuativeGeneric.isProper_of_lift_generic_of_finiteType <;> assumption)
end

