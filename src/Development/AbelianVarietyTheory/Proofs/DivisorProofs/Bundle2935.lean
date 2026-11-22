import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueHomogOfFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyValue_homog_of_fibres : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (K : Type) [Field K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (g : ℕ) (y y' : Fin g → (epsR K ⟶ G)) (x x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g) (a : K) (M : Matrix (Fin g) (Fin g) K), KeyOn (RingHom.id K) x G L σ (fun i => y (i.cast hg)) → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → (∀ i, IsLieComb (M i) y (y' i)) → a ^ 8 * (κ K x' : K) = M.det ^ 4 * κ K x := by
  intro κ hH hF K _ _ G _ _ L σ σ' g y y' x x' hg hg' a M hx hx' hσ hM
  subst hg
  have ha : a ≠ 0 := by
    rintro rfl
    exact GlobalTheory.T.keyDatum_false_of_modelSection_zero K G L σ' x' (fun i => y' (i.cast hg')) hx' (fun i => by rw [hσ i]; simp [constFn])
  obtain ⟨v, hv, hvM, hx1⟩ := GlobalTheory.T.exists_lieBasis_lift_model_vectors K G L σ σ' x x' hg' y y' M hx hx' hM
  have hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus (KeyOnPol.scale x.P.A.hom a x.th) :=
    fun s => (x.th_ne s).imp fun z hz => ⟨hz.1, KeyOnPol.mem_nonzeroLocus_of_unit x.P.A.hom (Units.mk0 a ha) (fun _ => rfl) hz.2⟩
  have hx2 := GlobalTheory.T.keyDatum_scale_sections_by_constant K G L σ σ' ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ y' a
    (KeyOnPol.scale x.P.A.hom a x.th) hth (fun _ => rfl) hσ hx1
  have hx'' : KeyOn ((RingHom.id K).comp (RingHom.id K)) x' G L σ' (fun i => y' (i.cast hg')) := by
    rwa [RingHom.id_comp]
  have hpb := GlobalTheory.T.keyDatum_fibre_of_composable_baseChange K K K (RingHom.id K) (RingHom.id K) G L σ' x.P.g y'
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyOnPol.scale x.P.A.hom a x.th, hth, v, hv⟩ x' rfl hg' hx2 hx''
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (KeyOnPol.scale x.P.A.hom a x.th) hth v hv a M
    (fun _ => rfl) hvM
  simp only [Nat.mul_one] at e2
  rw [e1, RingHom.id_apply]
  exact e2

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem exists_dir_eq_of_smooth : ∀ (k₀ : Type) [Field k₀] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k₀)) (n : ℕ),
    SmoothOfRelativeDimension n s → ∀ (K : Type) [Field K] (κ : k₀ →+* K) (ι : Type) [Fintype ι],
    Fintype.card ι = n → ∀ Xι : Spec (CommRingCat.of (TrivSqZeroExt K (ι → K))) ⟶ X,
    Xι ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K (ι → K)).comp κ)) →
    (∀ M M' : ι → K,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom) ≫ Xι → M = M') →
    ∀ x' : Spec (CommRingCat.of (DualNumber K)) ⟶ X,
    x' ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K K).comp κ)) →
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ x' =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι →
    ∃ M : ι → K, x' = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι := by
  intro k₀ _ X s n hs K _ κ ι _ hι Xι hXs hinj x' hx's hred
  have hloc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
    fun M _ _ _ _ => ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  have cp : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint (TrivSqZeroExt K M) := fun M _ _ _ _ => by
    haveI := hloc M
    exact IsLocalRing.comap_closedPoint _
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := hs.exists_isStandardSmoothOfRelativeDimension
    ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι) (IsLocalRing.closedPoint K))
  have h1 : Xι (IsLocalRing.closedPoint (TrivSqZeroExt K (ι → K))) ∈ V := by
    rw [← cp]; exact hxV
  have h2 : x' (IsLocalRing.closedPoint (DualNumber K)) ∈ V := by
    rw [← cp]; have := hxV; rw [← hred] at this; exact this
  obtain ⟨R, rfl⟩ := GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem X V hV _ Xι h1
  obtain ⟨g, rfl⟩ := GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem X V hV _ x' h2
  letI := (s.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) := hstd
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have mono : ∀ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {A : Type} [CommRing A] (φ ψ : Γ(Y, W) →+* A),
      Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec → φ = ψ := by
    intro Y W hW A _ φ ψ h
    have := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
    exact congrArg CommRingCat.Hom.hom this
  have hsp : ∀ {A : Type} [CommRing A] (φ : Γ(X, V) →+* A),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom (φ.comp (s.appLE U V e).hom)) ≫ hU.fromSpec := by
    intro A _ φ
    rw [Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
      (φ : Γ(X, V) →+* TrivSqZeroExt K M),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) →
      ∀ a, φ (s.appLE U V e a) = TrivSqZeroExt.inl (φ (s.appLE U V e a)).fst := by
    intro M _ _ _ _ φ hφ a
    have e1 := hsp φ
    have e2 : Spec.map (CommRingCat.ofHom (((TrivSqZeroExt.inlHom K M).comp (TrivSqZeroExt.fstHom K K M).toRingHom).comp
        (φ.comp (s.appLE U V e).hom))) ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← e1, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have := mono hU _ _ (e2.trans (hφ.symm.trans e1))
    exact (RingHom.congr_fun this a).symm
  obtain ⟨M, hM⟩ := GlobalTheory.T.square_zero_deformation_factors_through_linear Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) K n hstd ι hι R (hc _ R hXs)
    (fun M M' h => hinj M M' (by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, h]))
    g (fun b => by
      have := mono hV ((TrivSqZeroExt.fstHom K K K).toRingHom.comp g) ((TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R) (by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
        exact hred)
      exact RingHom.congr_fun this b)
    (hc _ g hx's)
  refine ⟨M, ?_⟩
  rw [hM, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem eq_of_isKS_eq : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''
  obtain ⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
      spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧
      ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
        GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
    first
    | exact GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq
    | exact GlobalTheory.T.universal_first_order_deformation hP E H Dw l Xo c K y hpq
    | exact (GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq)
  have htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X) := fun N => by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hX, sOf, sOf, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (GlobalTheory.FlagTan.dir c N).commutes _
    · rw [← Category.assoc, ← Spec.map_comp, ← hXy]
      congr 2
      ext z
      simp
  have uniq := fun x hx => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x hpq hx
  have key := exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom)
    (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X
    (by rw [hX, sOf])
    (fun N N' e => uniq _ (htan N) N N' (hXM N) (e ▸ hXM N'))
  have hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X := fun x hx =>
    key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)
  obtain ⟨N', rfl⟩ := hk x' h'
  obtain ⟨N'', rfl⟩ := hk x'' h''
  rw [uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem Trait.exists_lift {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (F : Type) [Field F] [Algebra (FractionRing W) F] (z : Sp F ⟶ C.G.left)
    (hz : z ≫ C.G.hom = jFK (R := W) F ≫ jK W ≫ T.ξ) :
    ∃ x : TFK (R := W) F ⟶ T.A.A, x.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z := by
  have w₁ : z ≫ C.G.hom = (jFK (R := W) F ≫ jK W) ≫ T.ξ := by rw [hz, Category.assoc]
  have w₂ : T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁ ≫ T.G.hom = jFK (R := W) F ≫ jK W :=
    T.cart.1.lift_snd _ _ _
  let g₂ : Sp F ⟶ pullback T.G.hom (jK W) := pullback.lift (T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁) (jFK (R := W) F) w₂
  have hs : T.U.gen.hom.left ≫ T.A.A.hom = pullback.snd T.G.hom (jK W) := Over.w T.U.gen.hom
  have hgi : T.U.gen.hom.left ≫ T.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨Over.homMk (g₂ ≫ T.U.gen.hom.left) (by
    show (g₂ ≫ T.U.gen.hom.left) ≫ T.A.A.hom = jFK (R := W) F
    rw [Category.assoc, hs]; exact pullback.lift_snd _ _ _), ?_⟩
  show (g₂ ≫ T.U.gen.hom.left) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z
  rw [Category.assoc, reassoc_of% hgi, pullback.lift_fst_assoc]
  exact T.cart.1.lift_fst _ _ _

end GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

theorem labExt_of_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], Nonempty (Trait C W) →
    ∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ (C.lab j) (C.lab j) := by
  intro R _ _ _ hR D C j W _ _ _ ⟨T⟩ σ p q hpq
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap T.inj)).toAlgebra
  have cF : Compat T.φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap T.inj r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) (Kb W)
  obtain ⟨r, hr⟩ := exists_ext hB em q
  have hr' : QkExt (em.comp σ).toRingHom p r := qkExt_trans hpq hr
  have hr₁ := isPullGtF_pullGt T.hD hGF cF r.g

  have hgp : jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ = jFK (R := R) (Kb W) ≫ C.gp := by
    let ρ : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp T.φ)
    have hρ : Function.Injective ρ :=
      (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
    have hy : (jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ) ≫ C.π = spMap ρ := by
      rw [Category.assoc, Category.assoc, T.ξ_π, spMap_comp, spMap_comp]
    obtain ⟨ga, hga, e⟩ := Modif.factor_gp R C.toModif (Kb W) ρ _ hρ hy
    have hga' : ga = algebraMap (FractionRing R) (Kb W) :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun s => (hga s).trans (cF s).symm)
    rw [e, hga']
  have hz : ∀ (τ : Kb R →ₐ[FractionRing R] Kb W) (x : TFK (R := R) (Kb R) ⟶ C.A.A),
      (spMap τ.toRingHom ≫ x.left ≫ C.α) ≫ C.G.hom = jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ := by
    intro τ x
    rw [hgp, Category.assoc, Category.assoc, C.α_cart.1.w, ← Category.assoc x.left, Over.w x, ← Category.assoc]
    show (spMap τ.toRingHom ≫ spMap (algebraMap (FractionRing R) (Kb R))) ≫ C.gp = _
    rw [← spMap_comp]; exact congrArg (fun f => spMap f ≫ C.gp) τ.comp_algebraMap
  obtain ⟨x₁, hx₁⟩ := T.exists_lift (Kb W) _ (hz em (C.lab j q))
  obtain ⟨x₂, hx₂⟩ := T.exists_lift (Kb W) _ (hz (em.comp σ) (C.lab j p))
  have t₁ := T.lab (Kb W) em cF j q r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₁ hr rfl hr₁ hx₁
  have t₂ := T.lab (Kb W) (em.comp σ) cF j p r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₂ hr' rfl hr₁ hx₂
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ bW T.D' T.A T.G hGs T.U (Kb W) (C.n ^ j) hk
  have e : x₁ = x₂ := ((hf.1 _ _).1 t₁).trans ((hf.1 _ _).1 t₂).symm
  subst e
  have e' := hx₁.symm.trans hx₂
  haveI : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (spMap em.toRingHom)).1 (C.α_cart.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, e', Category.assoc, ← Category.assoc (spMap em.toRingHom), ← spMap_comp]
    rfl
  · rw [Category.assoc, Over.w (C.lab j q), Category.assoc, Category.assoc, Over.w (C.lab j p)]
    exact congrArg (spMap em.toRingHom ≫ ·) ((spMap_comp _ _).symm.trans (congrArg spMap σ.comp_algebraMap)).symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
namespace GlobalTheory.LabelTransfer

theorem isAlgebraic_padicAlgCl (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V)
    [Algebra (FractionRing V) (PadicAlgCl p)]
    (hV : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    Algebra.IsAlgebraic (FractionRing V) (PadicAlgCl p) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨P, hP0, hPz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) z
  set κ := algebraMap (FractionRing V) (PadicAlgCl p)
  have hl : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) ∈ Polynomial.lifts κ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV _
  obtain ⟨P', hP'⟩ := hl
  rw [Polynomial.coe_mapRingHom] at hP'
  refine ⟨P', fun h => hP0 ?_, ?_⟩
  · have : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) = 0 := by rw [← hP', h, Polynomial.map_zero]
    exact (Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).1 this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval z (P'.map κ) = 0
    rw [hP', ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hPz]

end GlobalTheory.LabelTransfer

namespace GlobalTheory.LabelTransfer

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  intro o Ω _ _ _ S ρ p _ y₀ u eA s H F _ _ _ k hk _ q q' a a' hq hq' haa
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : Algebra.IsAlgebraic (FractionRing u.V) (PadicAlgCl p) :=
    isAlgebraic_padicAlgCl p u.V u.complete u.norm_le
  let emb : PadicAlgCl p →ₐ[FractionRing u.V] F := IsAlgClosed.lift
  letI : Algebra (PadicAlgCl p) F := emb.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing u.V) (PadicAlgCl p) F :=
    IsScalarTower.of_algebraMap_eq fun c => (emb.commutes c).symm
  have hf : (algebraMap (PadicAlgCl p) F).comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) =
      algebraMap (FractionRing u.V) F := (IsScalarTower.algebraMap_eq _ _ _).symm
  have hk0 : ((k : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q
  obtain ⟨q₀', hq₀'⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q'
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) k hk
  obtain ⟨f₁, hf₁, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U F k hk
  have hL := GlobalTheory.firstFiveLaws
  have e₁ : QkToAkU u.U.toUnifPre F k q (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀) :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀ _).1 ((hf₀ _ _).2 rfl)
  have e₂ : QkToAkU u.U.toUnifPre F k q' (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀') :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀' _).1 ((hf₀ _ _).2 rfl)
  have ha : a = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀ :=
    ((hf₁ _ _).1 hq).trans ((hf₁ _ _).1 e₁).symm
  have ha' : a' = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀' :=
    ((hf₁ _ _).1 hq').trans ((hf₁ _ _).1 e₂).symm
  have hepi : Epi (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left := by
    have : Flat (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    have : Surjective (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      ⟨fun z => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _⟩⟩
    have : QuasiCompact (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    exact Flat.epi_of_flat_of_surjective _
  have hx : (f₀ q₀).left = (f₀ q₀').left ≫ eA.left := by
    rw [ha, ha', Over.comp_left, Over.comp_left, Category.assoc] at haa
    exact (cancel_epi _).1 haa
  have := H k q₀' q₀ (f₀ q₀') (f₀ q₀) hk ((hf₀ _ _).2 rfl) ((hf₀ _ _).2 rfl) hx
  rw [hq₀.1, hq₀'.1]
  exact this

end GlobalTheory.LabelTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AllEmb

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

theorem lab_indep_level {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (hB : D.TauBimult) {A : PolAV (Sp (FractionRing R))} {lab : Labels D A}
    (hlab : ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D (Kb R) k), QkExt σ.toRingHom p p' →
      (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left)
    (τ₁ τ₂ : Kb R →ₐ[FractionRing R] F) {p q : QkPt D (Kb R) k} {r : QkPt D F k}
    (h₁ : QkExt τ₁.toRingHom p r) (h₂ : QkExt τ₂.toRingHom q r) :
    spMap τ₁.toRingHom ≫ (lab k p).left = spMap τ₂.toRingHom ≫ (lab k q).left := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Kb R →ₐ[FractionRing R] Kb R, τ₂.toRingHom.comp σ.toRingHom = τ₁.toRingHom := by
    letI : Algebra (Kb R) F := τ₂.toRingHom.toAlgebra
    haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (τ₂.commutes x).symm
    exact ⟨τ₁.restrictNormal (Kb R), RingHom.ext fun x => τ₁.restrictNormal_commutes (Kb R) x⟩
  obtain ⟨q', hq'⟩ := exists_ext hB σ p
  obtain ⟨r', hr'⟩ := exists_ext hB τ₂ q'
  have h₃ := qkExt_trans hq' hr'
  rw [hσ] at h₃
  obtain rfl := ext_unique hB τ₁ h₁ h₃
  obtain rfl := qkExt_inj hB τ₂ h₂ hr'
  rw [hlab σ p q hq', ← Category.assoc, ← Geo.Tor.spMap_comp, hσ]

theorem induces_of_one_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn _ _ hlab W _ _ _ hW φ iφ _ G' _ _ D' A' U' a hG ⟨ga, hga, gpa, _⟩ hD j
    ⟨C, _, _, _, _, emC, cC, HC⟩ F _ _ _ _ em cF p p₁ p' x' y₁ y₂ y₃ y₄
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  have := hR.2
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have cK : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨e⟩ := nonempty_lift (FractionRing R) (Kb W)

  have fac : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      algebraMap (FractionRing R) L = (algebraMap (FractionRing W) L).comp ga := fun L _ _ _ c =>
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c r).trans
      (congrArg (algebraMap (FractionRing W) L) (hga r).symm))
  have up : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      ∀ i : Kb W →ₐ[FractionRing W] L, ∃ i' : Kb W →ₐ[FractionRing R] L, i'.toRingHom = i.toRingHom := fun L _ _ _ c i =>
    ⟨⟨i.toRingHom, fun t => by rw [fac L c]; exact i.commutes (ga t)⟩, rfl⟩

  have key : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L],
      Compat φ L → ∀ (i : Kb W →ₐ[FractionRing W] L) (m : Kb R →ₐ[FractionRing R] L)
      (q : QkPt D.toPre (Kb R) (n ^ j)) (q₁ : QkPt D.toPre (Kb W) (n ^ j)) (x₀ : TFK (R := W) (Kb W) ⟶ A'.A),
      QkExt e.toRingHom q q₁ → x₀.left ≫ a = spMap e.toRingHom ≫ (lab (n ^ j) q).left →
      ∀ (s : QkPt D.toPre (Kb R) (n ^ j)) (s₁ : QkPt D.toPre L (n ^ j)) (s' : QkPt D'.toPre L (n ^ j))
        (z : TFK (R := W) L ⟶ A'.A), QkExt i.toRingHom q₁ s₁ → QkExt m.toRingHom s s₁ → s'.y = hD.xe.symm s₁.y →
        IsPullGtF φ hD L s₁.g s'.g → z.left ≫ a = spMap m.toRingHom ≫ (lab (n ^ j) s).left →
        (QkToAkU U'.toUnifPre (Kb W) (n ^ j) (pullQk hD hGF cK hB hB' q₁) x₀ ↔ QkToAkU U'.toUnifPre L (n ^ j) s' z) := by
    intro L _ _ _ _ c i m q q₁ x₀ hq hx₀ s s₁ s' z w₀ w₁ w₂ w₃ w₄
    obtain ⟨i', hi'⟩ := up L c i
    obtain ⟨⟨t, ht⟩, -, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG U' _ L i (n ^ j) hk
      (pullQk hD hGF cK hB hB' q₁)
    have t₁ : IsPullGtF φ hD L s₁.g t.g :=
      isPullGtF_ext hD c i.toRingHom i.comp_algebraMap (isPullGtF_pullGt hD hGF cK _) w₀ ht
    have t₂ : t.y = hD.xe.symm s₁.y := by rw [ht.1, w₀.1]; rfl
    obtain rfl : s' = t := ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨w₂, w₃⟩).trans
      ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨t₂, t₁⟩).symm
    have u : QkExt (i'.comp e).toRingHom q s₁ := by
      have := qkExt_trans hq w₀
      rw [← hi'] at this
      exact this
    have l := lab_indep_level hB (fun σ => hlab σ j) m (i'.comp e) w₁ u
    refine hgal s' x₀ z ht ?_
    apply gpa.1.hom_ext
    · rw [w₄, Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp, l, ← hi']
      rfl
    · rw [Category.assoc, Over.w z, Over.w x₀]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap i.comp_algebraMap)).symm
  obtain ⟨i⟩ := nonempty_lift (FractionRing W) F
  obtain ⟨i₀⟩ := nonempty_lift (FractionRing W) C
  obtain ⟨i', hi'⟩ := up F cF i
  obtain ⟨i₀', hi₀'⟩ := up C cC i₀
  obtain ⟨q₁, hq₁⟩ := exists_of_ext hB i' hk p₁
  obtain ⟨q, hq⟩ := exists_of_ext hB e hk q₁
  obtain ⟨x₀, hx₀⟩ := exists_lift_pt gpa.1 e.toRingHom e.comp_algebraMap (lab (n ^ j) q)
  obtain ⟨r₁, hr₁⟩ := exists_ext hB i₀' q₁
  obtain ⟨r, hr⟩ := exists_of_ext hB emC hk r₁
  obtain ⟨z, hz⟩ := exists_lift_pt gpa.1 emC.toRingHom (emC.comp_algebraMap.trans (fac C cC)) (lab (n ^ j) r)
  have hC := HC r r₁ (pullQk hD hGF cC hB hB' r₁) z hr rfl (isPullGtF_pullGt hD hGF cC _) hz
  exact (key F cF i em q q₁ x₀ hq hx₀ p p₁ p' x' (hi' ▸ hq₁) y₁ y₂ y₃ y₄).1
    ((key C cC i₀ emC q q₁ x₀ hq hx₀ r r₁ _ z (hi₀' ▸ hr₁) hr rfl (isPullGtF_pullGt hD hGF cC _) hz).2 hC)

end GlobalTheory.Mum.AllEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMinorsUnipotentMulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minors_unipotent_mul : ∀ (R : Type) [CommRing R] (m : ℕ) (n : Low m → R) (M : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → ∀ l : Fin (m + 1), ((uniR n * M).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det = (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  first | exact @GlobalTheory.FlagCell.det_leading_uniR_mul | exact GlobalTheory.FlagCell.det_leading_uniR_mul | (intros; apply GlobalTheory.FlagCell.det_leading_uniR_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  first | exact @GlobalTheory.Mum.qkPt_algClosure_bijective | exact GlobalTheory.Mum.qkPt_algClosure_bijective | (intros; apply GlobalTheory.Mum.qkPt_algClosure_bijective <;> assumption)
end

