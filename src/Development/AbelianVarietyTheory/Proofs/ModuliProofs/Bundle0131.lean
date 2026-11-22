import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DataAtTraitsOfTraitData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem sp_sq {A B B' C : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] {f : A →+* B} {g : B →+* C}
    {f' : A →+* B'} {g' : B' →+* C} (e : ∀ a, g (f a) = g' (f' a)) : spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  rw [← spMap_comp, ← spMap_comp]; exact congrArg spMap (RingHom.ext e)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

theorem isProper_of_range {X S X' S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {χ : S' ⟶ S} {F : X' ⟶ X}
    (h : IsPullback F p' p χ) (U : S.Opens) [IsProper (p ∣_ U)] (hU : Set.range χ ⊆ U) : IsProper p' := by
  have h₁ := (isPullback_morphismRestrict p U).flip
  have e : IsOpenImmersion.lift U.ι χ (by rwa [Scheme.Opens.range_ι]) ≫ U.ι = χ := IsOpenImmersion.lift_fac _ _ _
  rw [← e] at h
  have w := h.w
  rw [← Category.assoc] at w
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_right (by rw [h₁.lift_fst]; exact h) (h₁.lift_snd _ _ w) h₁) ‹_›

theorem arcDataAt_of_hasArcData {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W] (f : O' →+* W) (u : W) {χ : Sp W ⟶ Y.X} {v : Sp (FractionRing W) ⟶ Xo.XF c}
    (hv : v ≫ Y.j = Out.jK W ≫ χ) (h : Y.HasArcData a (IsLocalRing.maximalIdeal W) f u χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections.ArcDataAt Xo a f u (v ≫ pullback.fst _ _) := by
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨t', m₁, n, m₂, e₁, e₂⟩ := exists_generic Y m hv
  refine ⟨t, t', m₁, m₂, P, φ, he, w, e, h1, h2, h3, h4, h5, fun F _ _ _ _ uF hf hu => ?_⟩
  obtain ⟨k₁, k₂⟩ := h6 F uF hf hu
  refine ⟨k₁, fun k p₀ σ hσ q₀ q x x' hq hy hz hx₁ hx₂ => ?_⟩
  have : IsPreimmersion (Out.jK W) :=
    IsPreimmersion.of_isLocalization (R := W) (S := FractionRing W) (nonZeroDivisors W)
  have hb : x' ≫ t'.G.hom = Out.jFK (R := W) F := by
    rw [← cancel_mono (Out.jK W), Category.assoc, ← m₁.cart.1.w, ← Category.assoc]
    refine (congrArg (· ≫ t.G.hom) hx₁).trans ?_
    have w₁ : P.U.gen.inv.left ≫ pullback.snd t.G.hom (Out.jK W) = P.A.A.hom := Over.w P.U.gen.inv
    have w₂ : x.left ≫ P.A.A.hom = Out.jFK (R := W) F := Over.w x
    simp only [Category.assoc]
    rw [pullback.condition, ← w₂, ← w₁]
    simp only [Category.assoc]
  have key : ∀ σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ'.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ σ.left →
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK W) ≫ m.φ =
        (Out.jFK (R := W) F ≫ v) ≫ σ'.left ≫ Y.m.φ := fun σ' hσ' => by
    have w₃ : σ'.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ'
    have hn : x' ≫ n.φ = (Out.jFK (R := W) F ≫ v) ≫ σ'.left := by
      apply Y.m0.cart.1.hom_ext
      · refine (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) e₂.symm).trans (hx₂.trans ?_))
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hσ')).symm
        simp only [Category.assoc]
      · refine (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) n.cart.1.w).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w₃).trans (Category.comp_id _))).symm
        rw [← Category.assoc, hb]
    refine Eq.trans ?_ ((congrArg (· ≫ Y.m.φ) hn).trans (Category.assoc _ _ _))
    rw [Category.assoc, ← e₁, ← Category.assoc x', hx₁]
    simp only [Category.assoc]
  have hyF : (Out.jFK (R := W) F ≫ v) ≫ Y.j = Out.jFK (R := W) F ≫ Out.jK W ≫ χ := by
    rw [Category.assoc, hv]
  rcases hσ with ⟨hk, z, hp, rfl⟩ | ⟨hk, z, hz', hp, rfl⟩
  · exact k₂ _ hyF k p₀ _ (.inl ⟨hk, z, hp, rfl⟩) q₀ q x hq hy hz (key _ (Y.m0.etaA z))
  · exact k₂ _ hyF k p₀ _ (.inr ⟨hk, z, hz', hp, rfl⟩) q₀ q x hq hy hz (key _ (Y.m0.eta z))

theorem exists_ext {R₁ : Type} [CommRing R₁] [IsDomain R₁] {r : O →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}
    (h : y₁ ≫ pullback.snd _ _ ≫ spMap β = Out.jK R₁ ≫ spMap r) {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (ρ : R₁ →+* W) (κ : FractionRing R₁ →+* FractionRing W)
    (hκ : ∀ x, κ (algebraMap R₁ _ x) = algebraMap W _ (ρ x)) :
    ∃ χ : Sp W ⟶ Y.X, spMap κ ≫ y₁ ≫ Y.j = Out.jK W ≫ χ := by
  let fK : c.F →+* FractionRing W := (Spec.preimage (spMap κ ≫ y₁ ≫ pullback.snd _ _)).hom
  have hf : spMap fK = spMap κ ≫ y₁ ≫ pullback.snd _ _ := Spec.map_preimage _
  have ho : (algebraMap W (FractionRing W)).comp (ρ.comp r) = fK.comp β := by
    have e : spMap ((algebraMap W (FractionRing W)).comp (ρ.comp r)) = spMap (fK.comp β) := by
      rw [spMap_comp _ fK, hf, Category.assoc, Category.assoc, h, ← Category.assoc,
        sp_sq (f := algebraMap R₁ (FractionRing R₁)) (g := κ) (f' := ρ) hκ]
      simp only [spMap_comp, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  obtain ⟨⟨χ, ⟨-, h₂⟩, -⟩, -⟩ := GlobalTheory.ValuativeExtension.valuation_extension E H D l Xo c _ _ Y W (FractionRing W) _ fK
    (spMap κ ≫ y₁) ho (by rw [hf, Category.assoc])
  exact ⟨χ, by rw [h₂, Category.assoc]⟩

theorem dataAtTraits_of_traitData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), (∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ IsProper (Y.t.G.hom ∣_ U)) → Function.Injective (g.comp (PowerSeries.C (R := O'))) → g PowerSeries.X ≠ 0 → GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections.DataAtTraits Xo a g y₁ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ _ b a R₁ _ _ g y₁ ⟨U, hU, hp⟩ hi hX h
  have h0 := h.1
  rw [j_s] at h0
  have : CharZero (FractionRing R₁) :=
    (RingHom.charZero_iff (Spec.preimage (y₁ ≫ pullback.snd _ _)).hom.injective).1 inferInstance
  refine ⟨RingHom.charZero (algebraMap R₁ (FractionRing R₁)), hi, hX, h0, fun W _ _ _ ρ κ hW => ?_⟩
  have hκ : ∀ x, κ (algebraMap R₁ _ x) = algebraMap W _ (ρ x) := RingHom.congr_fun hW.2
  have := hW.1.1
  obtain ⟨χ, hχ⟩ := exists_ext Y (r := (g.comp (PowerSeries.C (R := O'))).comp b)
    (h0.trans (by simp only [spMap_comp, Category.assoc])) ρ κ hκ
  obtain ⟨k₁, k₂⟩ := h.2 W hW.1 ρ κ hκ χ hχ
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · obtain ⟨W', _, _, _, io, hW', ioi, iof, hd⟩ := k₂ hu
    have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp io) := (IsFractionRing.injective W' _).comp ioi
    let jo : FractionRing W →+* FractionRing W' := IsFractionRing.lift hinj
    have hjo : ∀ x, jo (algebraMap W _ x) = algebraMap W' _ (io x) := IsFractionRing.lift_algebraMap hinj
    refine ⟨W', inferInstance, inferInstance, inferInstance, io, jo.comp κ, ioi, iof,
      ⟨hW', RingHom.ext fun x => (congrArg jo (hκ x)).trans (hjo _)⟩, ?_⟩
    rw [← Category.assoc]
    refine arcDataAt_of_hasArcData Y a _ _ ?_ hd
    rw [spMap_comp, Category.assoc, Category.assoc, hχ, ← Category.assoc, ← Category.assoc,
      sp_sq (f := algebraMap W (FractionRing W)) (g := jo) (f' := io) (g' := algebraMap W' (FractionRing W')) hjo]
  · obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ χ
    obtain ⟨t', m₁, -, m₂, -⟩ := exists_generic Y m ((Category.assoc _ _ _).trans hχ)
    rw [← Category.assoc]
    exact ⟨t, t', m₁, m₂, isProper_of_range m.cart.1 U (hU ▸ k₁ hu)⟩

end GlobalTheory.TraitDataIntrinsic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PrimePowerTorsion

theorem dense_torsion (hA : Out.AmpleSt) (hK : Out.KerPowSt) (hI : Out.IrredSt) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (l : ℕ) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) := by
  have := P.isAb.comm
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (x := x) (U := ⟨U, hU⟩) hx
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ Out.nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA K P N hN
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, ham⟩ : ∃ m : ℕ, 4 ≤ m ∧ a + m = l ^ (a + 4) := by
    have := Nat.lt_pow_self (n := a + 4) (show 1 < l by omega)
    exact ⟨l ^ (a + 4) - a, by omega, by omega⟩
  obtain ⟨t, ht⟩ := gen m hm x
  let p : (Out.baseOver (Sp K)).left := IsLocalRing.closedPoint K
  obtain ⟨t', ht'⟩ := gen (a + m) (by omega) ((1 : Out.baseOver (Sp K) ⟶ P.A).left p)
  have e := nonzeroLocus_secMul s t
  obtain ⟨b, hb, q, hq⟩ := TorsionDense.exists_mem_nonzeroLocus P hI hK (a + m) (by omega)
    (by rw [ham, Nat.cast_pow]; exact pow_ne_zero _ hlK)
    {x | ∃ j : ℕ, x ^ l ^ j = 1} (fun w hw b ⟨j, hb⟩ => ⟨a + 4 + j, by
      rw [mul_pow, pow_add, pow_mul w, ← ham, hw, one_pow, mul_comm _ (l ^ j), pow_mul, hb, one_pow,
        _root_.one_mul]⟩)
    (secMul s t) t' x (e.ge ⟨hs, ht⟩) 1 ⟨0, one_pow _⟩ p ht'
  exact ⟨b.left q, hle (e.le hq).1, Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

theorem dense_torsion_and_eq_one :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℕ), l.Prime → (l : K) ≠ 0 → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) ∧ ∀ f : P.A ⟶ P.A, (∀ (j : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), x ^ l ^ j = 1 → x ≫ f = 1) → f = 1 := by
  intro h1 _ K _ _ P l hl hlK
  have hD := dense_torsion h1.ample h1.kerPow h1.irred K P l hl.two_le hlK
  refine ⟨hD, fun f hf => Over.OverMorphism.ext ?_⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.proper
  let g : P.A ⟶ P.A := 1
  suffices IsDominant (equalizer.ι f.left g.left) from
    ext_of_isDominant_of_isSeparated P.A.hom ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left)
      (equalizer.condition _ _)
  refine ⟨Dense.mono (fun y hy => ?_) hD⟩
  obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
  have hxy : x.left ≫ f.left = x.left ≫ g.left :=
    congrArg CommaMorphism.left ((hf j x hx).trans (MonObj.comp_one x).symm)
  refine ⟨equalizer.lift x.left hxy q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

end GlobalTheory.PrimePowerTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpPrim

theorem matrix_identities {n : Type} [Fintype n] [DecidableEq n] {W m m' : Matrix n n ℤ}
    (hd : (W + W.transpose).det = 1) (h : (W + W.transpose) * m = W) (h' : (W + W.transpose) * m' = W.transpose) :
    m + m' = 1 ∧ m.transpose * (W + W.transpose) = (W + W.transpose) * m' := by
  set G := W + W.transpose with hG
  have hu : IsUnit G.det := by rw [hd]; exact isUnit_one
  have hT : G.transpose = G := by
    rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  constructor
  · have key : G * (m + m') = G := by rw [Matrix.mul_add, h, h']
    calc m + m' = G⁻¹ * (G * (m + m')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
      _ = 1 := by rw [key, Matrix.nonsing_inv_mul G hu]
  · have ht := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, hT] at ht
    rw [ht, h']

theorem prod_mul_prod {M : Type} [CommGroup M] {n : ℕ} (x : Fin n → M) {m m' : Matrix (Fin n) (Fin n) ℤ}
    (h : m + m' = 1) (u : Fin n) :
    (List.ofFn fun v => x v ^ m u v).prod * (List.ofFn fun v => x v ^ m' u v).prod = x u := by
  have hm : ∀ v, m u v + m' u v = if u = v then 1 else 0 := by
    intro v
    have e := congrFun (congrFun h u) v
    rwa [Matrix.add_apply, Matrix.one_apply] at e
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  simp_rw [← zpow_add, hm]
  rw [Finset.prod_eq_single u (fun v _ hv => by rw [if_neg (Ne.symm hv), zpow_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), if_pos rfl, zpow_one]

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k h : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem isSharp_of_tmap {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t t' : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) (m : TMap t' t (𝟙 _)) : IsSharp W a bas t' c := by
  obtain ⟨φ, hpb, hLφ, hpt, hact⟩ := m
  obtain ⟨pr, hpr, huniv, hL, hpa, hlev⟩ := H
  have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, heφ'⟩ := grpPullback_iso hpb (isGrpPullback_of_iso (Iso.refl t.A))
  have heφ : e.hom.left = φ := by simpa using heφ'
  have hcomm : ∀ j, t'.act j ≫ e.hom = e.hom ≫ t.act j := by
    intro j
    ext
    simp only [Over.comp_left, heφ, hact j]
  refine ⟨fun u => e.hom ≫ pr u, fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hpr u
    infer_instance
  · obtain ⟨x0, hx0, hu0⟩ := huniv T y
    refine ⟨x0 ≫ e.inv, fun u => by simpa using hx0 u, fun x hx => ?_⟩
    have hx' : x ≫ e.hom = x0 := hu0 _ fun u => by simpa using hx u
    rw [← hx']
    simp
  · have hfun : (fun uv : Fin 8 × Fin 8 => (lift (e.hom ≫ pr uv.1) (e.hom ≫ pr uv.2)).left) =
        fun uv => φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      funext uv
      rw [← comp_lift, Over.comp_left, heφ]
    rw [hfun]
    refine (CechPic.cls_eq_iff t'.isLB (LB.isLB_linComb c.isLB _ _)).1 ?_
    rw [(CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB φ)).2 hLφ, CechPic.cls_pull t.isLB,
      (CechPic.cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL,
      CechPic.cls_linComb c.isLB, CechPic.cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← CechPic.pull_comp]
  · rw [← Category.assoc, hcomm j, Category.assoc, hpa j u, PowerAdjoint.comp_prod_zpow]
  · have hp := hpt i
    rw [Category.id_comp] at hp
    rw [← hlev i u, Over.comp_left, Over.comp_left, heφ, ← Category.assoc, hp, Over.comp_left]

end GlobalTheory.SharpPrim

theorem GlobalTheory.sharpClass_prim_and_iso : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  intro hΘ o _ g k J b em w w' h W a bas t ht
  obtain ⟨c, hc, hs⟩ := ht
  refine ⟨fun hE hw hw' => ?_, fun t' m => ⟨c, hc, SharpPrim.isSharp_of_tmap hs m⟩⟩
  obtain ⟨pr, hpr, huniv, hL, hact, -⟩ := hs
  have hid := SharpPrim.matrix_identities hE.2 hw hw'
  have key := PowerAdjoint.matrix_primitive_adjoint hΘ W ℂ o (spMap em) h k (b.ζ : o) c t.pol pr hpr huniv hL
    (a w) (t.act w) (hact w)
  refine ⟨?_, key.2 (a w') (t.act w') (hact w') hid.2, key.1 hw⟩
  obtain ⟨x0, -, hu0⟩ := huniv t.A pr
  have h1 : ∀ u, (t.act w * t.act w') ≫ pr u = pr u := by
    intro u
    have := hpr u
    rw [MonObj.mul_comp, hact w u, hact w' u]
    exact SharpPrim.prod_mul_prod pr hid.1 u
  rw [hu0 _ h1, hu0 (𝟙 t.A) fun u => Category.id_comp _]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.eighthPower_integerMatrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  first | exact @GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | exact GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | (intros; apply GlobalTheory.PowerAdjoint.matrix_primitive_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AmpleDominates

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {X : Scheme.{0}} {M N : LB X}

theorem eventually_isGenerated {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsGenerated (LB.div (lbPow M t) N) := by
  obtain ⟨d, hd, m, s, hs⟩ := hM.exists_veryAmpleBy f
  have hH := isLB_lbPow hM.isLB d
  have hD : ∀ i, (LB.div (lbPow M i) N).IsLB := fun i => LB.isLB_div (isLB_lbPow hM.isLB i) hN
  choose t₀ ht₀ using fun i => TwistGen.twist_generated R X f _ m s hH hs _ (hD i)
  refine Filter.eventually_atTop.2 ⟨d * (Finset.range d).sup fun i => (t₀ i).toNat, fun t ht => ?_⟩
  have h₁ : (t₀ (t % d)).toNat ≤ t / d :=
    (Finset.le_sup (f := fun i => (t₀ i).toNat) (Finset.mem_range.2 (Nat.mod_lt t hd))).trans
      ((Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm]))
  obtain ⟨n, u, hu⟩ := ht₀ (t % d) (t / d : ℕ) (Int.toNat_le.1 h₁)
  have hG : IsGenerated (tw (LB.div (lbPow M (t % d)) N) (lbPow M d) (t / d : ℕ)) := ⟨_, u, hu⟩
  refine hG.of_lbIso (hD t) ((cls_eq_iff (hD t) hG.isLB).1 ?_)
  have e : cls _ hG.isLB = cls _ (hD (t % d)) - cls _ (isLB_pw hH (-((t / d : ℕ) : ℤ))) :=
    cls_div (hD _) (isLB_pw hH _) _
  rw [e, AmpleStabFinite.cls_pw hH, cls_div (isLB_lbPow hM.isLB t) hN, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_lbPow hM.isLB, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  generalize cls M hM.isLB = a
  generalize cls N hN = b
  conv_lhs => rw [← Nat.mod_add_div t d]
  module

theorem eventually_isAmpleLB {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsAmpleLB (LB.div (lbPow M t) N) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (eventually_isGenerated f hM hN)
  refine Filter.eventually_atTop.2 ⟨a + 1, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hG := ha k (by omega)
  have h₀ := LB.isLB_div (isLB_lbPow hM.isLB (k + 1)) hN
  have h₁ := LB.isLB_div h₀ hM.isLB
  refine hM.tensor_isGenerated hG h₀ ((cls_eq_zero_iff (LB.isLB_div h₁ hG.isLB)).1 ?_)
  rw [cls_div h₁ hG.isLB, cls_div h₀ hM.isLB, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_div (isLB_lbPow hM.isLB _) hN, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  module

theorem exists_sec_ne_zero [Nonempty X] {L : LB X} (h : IsGenerated L) : ∃ s : L.Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  refine ⟨s, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem eventually_sec_and_relAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  intro K _ _ P M N hM hN h
  have := P.isAb.proper
  have := polAV_isIntegral_of_isAlgClosed K P
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A hM h
  filter_upwards [eventually_isGenerated P.A.hom hA hN, eventually_isAmpleLB P.A.hom hA hN] with t h₁ h₂
  exact ⟨exists_sec_ne_zero h₁, (relAmple_iff_isAmpleLB_of_isAffine P.A h₂.isLB).2 h₂⟩

end GlobalTheory.AmpleDominates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfMemRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

private theorem exists_algClosed_compositum {k K K₀ : Type} [Field k] [Field K] [Field K₀]
    (φ : k →+* K) (ψ : k →+* K₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      i.comp φ = j.comp ψ := by
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra k K₀ := ψ.toAlgebra
  haveI : Nontrivial (K ⊗[k] K₀) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K K₀
      φ.injective ψ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K₀)
  letI : Field (K ⊗[k] K₀ ⧸ m) := Ideal.Quotient.field m
  let emb : K ⊗[k] K₀ →+* AlgebraicClosure (K ⊗[k] K₀ ⧸ m) :=
    (algebraMap (K ⊗[k] K₀ ⧸ m) (AlgebraicClosure (K ⊗[k] K₀ ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (K ⊗[k] K₀ ⧸ m), inferInstance, inferInstance,
    emb.comp Algebra.TensorProduct.includeLeftRingHom,
    emb.comp (Algebra.TensorProduct.includeRight : K₀ →ₐ[k] K ⊗[k] K₀).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  show (algebraMap k K a) ⊗ₜ[k] (1 : K₀) = (1 : K) ⊗ₜ[k] (algebraMap k K₀ a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private theorem pt_eq_lemma_2 {K : Type} [Field K] (q r : PrimeSpectrum K) : q = r :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime r.asIdeal).symm)

theorem exists_algClosed_join_of_mem_range {S : Scheme.{0}} {K K₀ : Type} [Field K] [Field K₀]
    (x : Sp K ⟶ S) (x₀ : Sp K₀ ⟶ S) (p : Sp K) (p₀ : Sp K₀) (h : x p = x₀ p₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : K₀ →+* Ω),
      spMap i ≫ x = spMap j ≫ x₀ := by
  have e : p = IsLocalRing.closedPoint K := pt_eq_lemma_2 _ _
  have e₀ : p₀ = IsLocalRing.closedPoint K₀ := pt_eq_lemma_2 _ _
  subst e e₀
  have hx := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x
  have hx₀ := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K₀ S x₀
  generalize S.descResidueField (Scheme.stalkClosedPointTo x) = φ at hx
  generalize S.descResidueField (Scheme.stalkClosedPointTo x₀) = φ₀ at hx₀
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ := exists_algClosed_compositum φ.hom ((S.residueFieldCongr h).hom ≫ φ₀).hom
  refine ⟨Ω, hΩ, hΩc, i, j, ?_⟩
  have hx₀' : Spec.map ((S.residueFieldCongr h).hom ≫ φ₀) ≫
      S.fromSpecResidueField (x (IsLocalRing.closedPoint K)) = x₀ := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hx₀]
  have hc : φ ≫ CommRingCat.ofHom i = ((S.residueFieldCongr h).hom ≫ φ₀) ≫ CommRingCat.ofHom j := by
    ext a
    exact RingHom.congr_fun hij a
  show Spec.map (CommRingCat.ofHom i) ≫ x = Spec.map (CommRingCat.ofHom j) ≫ x₀
  conv_lhs => rw [← hx]
  conv_rhs => rw [← hx₀']
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hc]

theorem geoGood_commonFibres : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t t' : TObj g k J b s), GeoGood t t' {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (u : TObj g k J b (x ≫ s)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} := by
  intro o _ g k J b S s t t' K _ x hx
  obtain ⟨K₁, hK₁, x₁, u₁, ⟨p₁, hp₁⟩, hu, hu'⟩ := hx ⟨IsLocalRing.closedPoint K, rfl⟩
  obtain ⟨Ω, hΩ, hΩc, i, j, hij⟩ :=
    exists_algClosed_join_of_mem_range x x₁ (IsLocalRing.closedPoint K) p₁ hp₁.symm
  obtain ⟨u, hu₀⟩ := GlobalTheory.tObj_pull o g k J b (Sp K₁) (Sp Ω) (x₁ ≫ s) (spMap i ≫ x ≫ s) (spMap j) u₁
    (by rw [← Category.assoc, ← hij, Category.assoc])
  have hT := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t u₁ u).2
    x₁ (spMap j) hu).1 hu₀
  have hT' := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S (Sp K₁) (Sp Ω) s (x₁ ≫ s) (spMap i ≫ x ≫ s) t' u₁ u).2
    x₁ (spMap j) hu').1 hu₀
  rw [← hij] at hT hT'
  obtain ⟨ψ, hψ⟩ := (tMap_iff u t _).1 hT
  obtain ⟨ψ', hψ'⟩ := (tMap_iff u t' _).1 hT'
  exact ⟨Ω, hΩ, hΩc, i, spMap i ≫ x ≫ s, u, ψ, ψ', hψ, hψ'⟩

end GlobalTheory.TUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.HkFam.isog_pull | exact GlobalTheory.HkFam.isog_pull | (intros; apply GlobalTheory.HkFam.isog_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecLbPowDivNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_nonzero_sec_lbPow_div : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.exists_sec_lbPow_div_ne_zero | exact GlobalTheory.exists_sec_lbPow_div_ne_zero | (intros; apply GlobalTheory.exists_sec_lbPow_div_ne_zero <;> assumption)
end

