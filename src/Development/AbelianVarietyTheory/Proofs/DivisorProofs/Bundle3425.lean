import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDer

theorem logDer_extend_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  intro E _ _ _ H Dw l Xo c Y U D k _ m d ξ hx hE hI
  have hiso : IsIso (genι Y) := isIso_fst Y
  set x := ξ (closedPoint _) with hxdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_derivation_stalk_extend_of_app _ _ (genι Y) U D.1 x hx
  set g := ((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) x hx).hom.comp ((genι Y).app U.1).hom with hg
  have hZ : ((genBd Y : TopologicalSpace.Closeds (gen Y)) : Set (gen Y)) = (genι Y) ⁻¹' ((interior Y).compl : Set Y.X) := by
    ext z
    simp only [TopologicalSpace.Opens.coe_compl, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [mem_genBd]
    unfold GlobalTheory.LogKS.interior Model.j
    have hc : ∀ w, (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) w = genι Y (Y.jQ w) := fun w => rfl
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range, hc]
    constructor
    · rintro h ⟨w, hw⟩
      exact h ⟨w, (genι Y).isOpenEmbedding.injective hw⟩
    · rintro h ⟨w, hw⟩
      exact h ⟨w, by rw [← hw]; rfl⟩
  have hJ := GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso _ _ (genι Y) _ (genBd Y) hZ U x hx
  have hstab : ∀ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g,
      δ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have := hδ r
      simp only [hg, RingHom.comp_apply] at this ⊢
      rw [this]
      exact Ideal.mem_map_of_mem _ (D.2.2 r hr)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
    | smul c y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')
  have hC : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hk : CharZero k := (RingHom.charZero_iff (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))).2 hC
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_extension_completedEtaleChart _ k m d (Scheme.stalkClosedPointTo ξ).hom hE δ
  refine ⟨D', fun r => ?_, GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span _ k m d _ δ D' _ hstab hD' (by rw [← hJ]; exact hI)⟩
  simp only [RingHom.comp_apply]
  rw [hD']
  exact congrArg _ (hδ r)

end GlobalTheory.ChartDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundaryStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_abelianLocus_toricChart_iff_not_mem_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  first | exact @GlobalTheory.ChartAbLocus.mem_abLocus_iff | exact GlobalTheory.ChartAbLocus.mem_abLocus_iff | (intros; apply GlobalTheory.ChartAbLocus.mem_abLocus_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem mem_primDR_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  intro A _ g L u hA c p hp
  obtain ⟨n, L', v, M₁, M₂, hAA, h1, h2, h3, hM1, hM2⟩ := GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety A g L u hA
  rw [mem_prim_iff]
  have key : ∀ (φ : A ⊗ A ⟶ A) (M : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (_hw : ∀ w, u.ex (M w) = v.ex w ≫ φ)
      (hM : ∀ l : v.Λ, M l ∈ u.Λ),
      IsPer v.ex v.Λ (cmp1 (str (A ⊗ A)) (pullOver (dp0 ℂ) (𝟙 _) φ c)) (fun l ↦ p ⟨M l, hM l⟩) := by
    intro φ M hw hM
    have hm := IsMor.of_over (dp0 ℂ) (φ := φ.left) (s := str A) (s' := str (A ⊗ A))
      (by rw [← Category.assoc, Over.w])
    exact GlobalTheory.T.isPer_of_isPull1_of_isPer A g L u (A ⊗ A) n L' v φ M hm.w hw hM _ _ _ (comparison_pullback hm c) hp
  have hμ := key μ[A] (M₁ + M₂) h3 (fun l ↦ add_mem (hM1 l) (hM2 l))
  have hf := key (fst A A) M₁ h1 hM1
  have hs := key (snd A A) M₂ h2 hM2
  obtain ⟨hlin, -⟩ := GlobalTheory.T.cechDeRhamPeriods_linear (A ⊗ A) n L' v
  have hdiff := (hlin _ _ _ _ hμ (hlin _ _ _ _ hf hs).1).2
  have hq : ((fun l : v.Λ ↦ p ⟨(M₁ + M₂) l, add_mem (hM1 l) (hM2 l)⟩) -
      ((fun l : v.Λ ↦ p ⟨M₁ l, hM1 l⟩) + fun l : v.Λ ↦ p ⟨M₂ l, hM2 l⟩)) = 0 := by
    funext l
    rw [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_eq_zero, ← map_add]
    rfl
  rw [hq] at hdiff
  have h0 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero (A ⊗ A) n L' v hAA _ hdiff
  rw [← map_add, ← map_sub] at h0
  exact sub_eq_zero.1 ((GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex (A ⊗ A) hAA).1 (h0.trans (map_zero _).symm))

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  first | exact @GlobalTheory.HeatSym.VS.mul | exact GlobalTheory.HeatSym.VS.mul | (intros; apply GlobalTheory.HeatSym.VS.mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem exists_cubical (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj (A ⊗ B)] (hAB : IsAbelianScheme (A ⊗ B)) {P : LB (A ⊗ B).left} (hP : IsDual A B P) :
    ∃ M : RigLB (A ⊗ B), M.L = P ∧ Nonempty (CubicalStr (A ⊗ B) M) := by
  obtain ⟨r, hr⟩ : AbLaw.Triv (P.pull (eSec (A ⊗ B))) := by
    have e := (AbDual.triv_ev_iff hP.isLB _ _).2
      (AbDual.evc_one_right hP.isLB hP.zero (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ B) = η[A ⊗ B] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := triv_theta hC hAB hP.isLB
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hP.isLB t ht
  exact ⟨⟨P, r, hP.isLB, hr⟩, rfl, ⟨AbLaw.Cube.cubicalOfNormalised globalFns_holds hAB ⟨P, r, hP.isLB, hr⟩ t' ht' hn'⟩⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem cubWeil_eq_of_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hp : IsGrpPullback G' G f m.F) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} (hc : m.IsPullCubical c' c) {N : ℕ} {T : Over S} {T' : Over S'}
    (τ : T'.left ⟶ T.left) (hτ : τ ≫ T.hom = T'.hom ≫ f) {x y : T ⟶ G} {x' y' : T' ⟶ G'}
    (hx : x'.left ≫ m.F = τ ≫ x.left) (hy : y'.left ≫ m.F = τ ≫ y.left) {ζ : Γ(T.left, ⊤)ˣ} {ζ' : Γ(T'.left, ⊤)ˣ}
    (h : UU.CubWeil c N x y ζ) (h' : UU.CubWeil c' N x' y' ζ') :
    ζ' = Units.map τ.appTop.hom.toMonoidHom ζ := by
  have h₁ := UU.cubWeil_of_isPullCubical _ _ f G G' m hp.1.w (fun T a b =>
    Over.OverMorphism.ext (hp.2 T a b _ _ rfl rfl).symm) L L' c c' hc N T' x' y' ζ' h'
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  have h₂ := h.comp σ
  have e₁ : σ ≫ x = Out.toBase hp.1.w x' := Over.OverMorphism.ext hx.symm
  have e₂ : σ ≫ y = Out.toBase hp.1.w y' := Over.OverMorphism.ext hy.symm
  rw [e₁, e₂] at h₂
  exact h₁.unique h₂

theorem lift_left_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {h : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h₁ : h ≫ (fst G G).left = (fst G' G').left ≫ φ)
    (h₂ : h ≫ (snd G G).left = (snd G' G').left ≫ φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    {x y : T ⟶ G} {x' y' : T' ⟶ G'} (hx : x'.left ≫ φ = τ ≫ x.left) (hy : y'.left ≫ φ = τ ≫ y.left) :
    (lift x' y').left ≫ h = τ ≫ (lift x y).left := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_left_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    (hτ : τ ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = τ ≫ (1 : T ⟶ G).left := by
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  exact congrArg (fun q => q.left) ((map_one (pushHom hp T')).trans (MonObj.comp_one σ).symm)

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

theorem exists_unit (hC : GlobalTheory.Published.CubeTheorem) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} (hG : IsSemiAbelian G) (hp : IsGrpPullback A G (spMap (algebraMap R K)) φ)
    (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : IsDual A A P) {N : ℕ} {B : Type} [CommRing B] [Algebra R B]
    {x y : SpAlg R B ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) {D C : Type} [CommRing D] [Algebra K D] [CommRing C]
    [Algebra K C] {x' y' : SpAlg K D ⟶ A} (hx' : x' ^ N = 1) (hy' : y' ^ N = 1) {U : Dˣ}
    (hU : Out.WeilIs (A ⊗ A) P (N : ℤ) (T := SpAlg K D) (lift x' 1) (lift 1 y') (unitOn U))
    (g : D →ₐ[K] C) (f : B →+* C) (ex : (spOver g ≫ x').left ≫ φ = spMap f ≫ x.left)
    (ey : (spOver g ≫ y').left ≫ φ = spMap f ≫ y.left) : ∃ U' : Bˣ, g U.val = f U'.val := by
  have hAA := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hAA.comm
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have := hG.quasiCompact
  have := CubeExtension.smooth_tensor G G
  have := CubeExtension.geometricallyConnected_tensor G G
  have hq : QuasiCompact (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have := LBExtDVR.isOpenImmersion_spMap_fractionRing R K
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hp hp
  have hpp := isGrpPullback_prod hp hp h₁ h₂
  obtain ⟨L, rfl, ⟨c⟩⟩ := exists_cubical hC hAA hP
  obtain ⟨M, hM, iM⟩ := LBExtDVR.exists_lineBundle_extension_genericFibre R K _ _ (G ⊗ G).hom (A ⊗ A).hom h
    inferInstance hq hpp.1 L.L L.isLB
  obtain ⟨L', c', m, rfl, -, hc, -⟩ := NormalCubeExt.exists_cubical_extension (Sp R)
    ((isNormalScheme_iff_pred _).1 inferInstance) (Sp K) (spMap (algebraMap R K)) (G ⊗ G) (A ⊗ A) h hpp L c M hM iM
  have hτ : spMap f ≫ (SpAlg R B).hom = (SpAlg K C).hom ≫ spMap (algebraMap R K) := by
    rw [← Over.w x, ← Category.assoc, ← ex, Category.assoc, hp.1.w, ← Category.assoc, Over.w]
  have o := one_left_comm hp (T := SpAlg R B) (T' := SpAlg K C) (spMap f) hτ
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c' (lift_pow hx (one_pow N)) (lift_pow (one_pow N) hy)
  obtain ⟨U', rfl⟩ := EpsWeil.unitOn_bijective.2 ζ
  have k := ((UU.cubWeil_iff_weilIs (c := c) globalFns_holds hAA (lift_pow hx' (one_pow N))
    (lift_pow (one_pow N) hy') _).2 hU).comp (spOver g)
  rw [comp_lift, comp_lift, MonObj.comp_one] at k
  have e := cubWeil_eq_of_pull m hpp hc (T := SpAlg R B) (T' := SpAlg K C) (spMap f) hτ
    (lift_left_comm h₁ h₂ _ ex o) (lift_left_comm h₁ h₂ _ o ey) hζ k
  exact ⟨U', congrArg Units.val (EpsWeil.unitOn_bijective.1
    (((EpsWeil.map_unitOn (g : D →+* C) U).symm.trans e).trans (EpsWeil.map_unitOn f U')))⟩

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (B : Type) [CommRing B]

def twoMap [Algebra R B] : B ⊗[R] B →ₐ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight (R := K)).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ => .all _ _

theorem twoMap_tmul [Algebra R B] (a b : B) :
    twoMap (K := K) B (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [twoMap]

variable {B} [Bialgebra R B] [Module.Finite R B] [Module.Projective R B]

theorem contract_twoMap (χ : CartierDual R B) (u : B ⊗[R] B) :
    TensorProduct.rid K _ ((CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv.lTensor _ (twoMap (K := K) B u)) =
      (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ u) := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
  | tmul a b =>
    have := CartierDual.baseChange_tmul_tmul K 1 1 χ b
    rw [twoMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rid_tmul, rid_tmul]
    rw [show (CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv ((1 : K) ⊗ₜ b) = χ.ofConv b • (1 * 1 : K) from this,
      _root_.mul_one, smul_assoc, one_smul, tmul_smul]

theorem contract_map {D C : Type} [CommRing D] [Algebra K D] [CommRing C] [Algebra K C] (κ : D →ₐ[K] C)
    (ψ : C →ₗ[K] K) (u : D ⊗[K] D) :
    κ (TensorProduct.rid K _ ((ψ ∘ₗ κ.toLinearMap).lTensor _ u)) =
      TensorProduct.rid K _ (ψ.lTensor _ (Algebra.TensorProduct.map κ κ u)) := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

end Algebra

theorem finTower_pow {p : ℕ} {R : Type} [CommRing R] {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G]
    (s : FinTower Γ G) (n : ℕ) {B : Type} [CommRing B] [Algebra R B] (ψ : Γ.A n →ₐ[R] B) :
    (spOver ψ ≫ s.y n) ^ p ^ n = 1 := by
  let F : WithConv (Γ.A n →ₐ[R] B) →* (SpAlg R B ⟶ G) :=
    MonoidHom.mk' (fun φ => spOver φ.ofConv ≫ s.y n) (s.mul n B)
  exact (map_pow F (WithConv.toConv ψ) _).symm.trans ((congrArg F (Γ.pts_pow_self n _)).trans (map_one F))

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

theorem univ_left_comm {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}
    {s : FinTower Γ G} {t : 𝒜.TorsionTower A} {κ : Γ.baseChange K ⟶ 𝒜} (hκ : s.IsIncl t φ κ) (n : ℕ)
    {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (g : D →ₐ[K] C) (f : B →+* C) (i : 𝒜.A n →ₐ[K] D) (j : Γ.A n →ₐ[R] B) (l : K ⊗[R] Γ.A n →+* C)
    (e₁ : ∀ a, g (i a) = l (κ.app n a)) (e₂ : ∀ a, f (j a) = l ((1 : K) ⊗ₜ a)) :
    (spOver g ≫ spOver i ≫ t.y n).left ≫ φ = spMap f ≫ (spOver j ≫ s.y n).left := by
  have h := congrArg (spMap l ≫ ·) (hκ n)
  simp only [← Category.assoc, ← Cris.spMap_comp] at h
  simp only [Over.comp_left, PDiv.spOver_left, ← Category.assoc, ← Cris.spMap_comp]
  exact (congrArg (fun q => (spMap q ≫ (t.y n).left) ≫ φ) (RingHom.ext e₁)).trans
    (h.trans (congrArg (fun q => spMap q ≫ (s.y n).left) (RingHom.ext fun a => (e₂ a).symm)))

theorem comp_weilProj_app [Fact p.Prime] (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) (n : ℕ)
    (x : K ⊗[R] CartierDual R (Γ.A n)) : (κ ≫ weilProj κ w).app n x =
      κ.app n (w.app n (CartierDual.map (κ.app n) (CartierDual.baseChange R K (Γ.A n) x))) := rfl

theorem comp_weilProj_app_eq [Fact p.Prime] (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) (n : ℕ)
    {U : 𝒜.A n ⊗[K] 𝒜.A n}
    (hw : ∀ χ : CartierDual K (𝒜.A n), w.app n χ = TensorProduct.rid K _ (χ.ofConv.lTensor _ U))
    {U' : Γ.A n ⊗[R] Γ.A n} (e : Algebra.TensorProduct.map (κ.app n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n)
      (κ.app n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n) U = twoMap (K := K) (Γ.A n) U') (χ : CartierDual R (Γ.A n)) :
    (κ ≫ weilProj κ w).app n ((1 : K) ⊗ₜ χ) = (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ U') := by
  rw [comp_weilProj_app, hw, ← contract_twoMap, ← e, ← contract_map]
  rfl

end Level

theorem exists_baseChangeMap_eq_weilProj : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), s.IsIncl t φ κ → IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → ∀ w : 𝒜 ⟶ 𝒜.dual, IsWeilHom t t P w → ∃ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w := by
  intro hC p _ R _ _ _ K _ _ _ G _ A _ φ hG hp Γ s 𝒜 t κ hκ hA P hP w hw
  refine PDivDescend.exists_baseChangeMap_eq p R K Γ Γ.dual _ fun n χ => ?_
  obtain ⟨U, hU, hwU⟩ := hw n
  let κ' : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n := κ.app n
  have pw : ∀ {D : Type} [CommRing D] [Algebra K D] (ψ : 𝒜.A n →ₐ[K] D), (spOver ψ ≫ t.y n) ^ p ^ n = 1 :=
    fun ψ => by rw [← MonObj.comp_pow, t.y_pow, MonObj.comp_one]
  have e₁ := univ_left_comm hκ n (Algebra.TensorProduct.map κ' κ') (twoMap (R := R) (K := K) (Γ.A n)).toRingHom
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeftRingHom
    (fun a => by simp [κ']) fun a => twoMap_tmul _ a 1
  have e₂ := univ_left_comm hκ n (Algebra.TensorProduct.map κ' κ') (twoMap (R := R) (K := K) (Γ.A n)).toRingHom
    Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight (R := K)).toRingHom
    (fun a => by simp [κ']) fun a => twoMap_tmul _ 1 a
  obtain ⟨U', e⟩ := exists_unit hC hG hp hA hP (finTower_pow s n _) (finTower_pow s n _) (pw _) (pw _) hU _ _ e₁ e₂
  exact ⟨_, comp_weilProj_app_eq κ w n hwU e χ⟩

end GlobalTheory.WeilIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDerivationsEqZeroKillingBothFactors
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBaseChangeLocal

theorem top_le_of_mem {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} (g₀ : Sp S ⟶ Y) (V : Y.Opens)
    (hV : g₀.base (IsLocalRing.closedPoint S) ∈ V) : ⊤ ≤ g₀ ⁻¹ᵁ V := by
  intro x _
  have hs : x ⤳ IsLocalRing.closedPoint S :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  exact (hs.map g₀.base.hom.continuous).mem_open V.isOpen hV

theorem valR_one_of_le {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (O : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) : valR x O 1 = 1 := by
  simp only [valR, dif_pos h, map_one]

theorem eq_zero_of_kills_both : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (W₀ : Z.Opens), W₀ ≤ p ⁻¹ᵁ U.1 → ∀ (O : Z'.Opens), O ≤ φ ⁻¹ᵁ W₀ ⊓ p' ⁻¹ᵁ U'.1 → ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₀ : Sp S ⟶ Z'), ⊤ ≤ g₀ ⁻¹ᵁ O → ∀ (Δ : ∀ O' : Z'.Opens, Γ(Z', O') → S), (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f + f') = Δ O' f + Δ O' f') → (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f * f') = valR g₀ O' f * Δ O' f' + valR g₀ O' f' * Δ O' f) → (∀ (O₁ O₂ : Z'.Opens) (h : O₂ ≤ O₁), O₁ ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O₂ → ∀ f, Δ O₂ (resG Z' h f) = Δ O₁ f) → (∀ (O₀ : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O₀), O₀ ≤ W₀ → O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f₀, Δ O' ((φ.appLE O₀ O' h).hom f₀) = 0) → (∀ (O' : Z'.Opens) (h : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ r, Δ O' ((p'.appLE U'.1 O' h).hom r) = 0) → ∀ f, Δ O f = 0 := by
  intro Z Z' X X' p p' φ g hpb U U' hU'U W₀ hW₀ O hO S _ _ g₀ hg₀ Δ hadd hmul hres hφ hp' f
  set m := IsLocalRing.closedPoint S
  have hz : g₀.base m ∈ O := hg₀ (Set.mem_univ m)
  have hzW : φ.base (g₀.base m) ∈ W₀ := (hO hz).1
  obtain ⟨O₀, hO₀a, hzO₀, hO₀W⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hzW
  obtain ⟨hA, hcl⟩ := GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU'U ⟨O₀, hO₀a⟩ (hO₀W.trans hW₀)
  set A := φ ⁻¹ᵁ O₀ ⊓ p' ⁻¹ᵁ U'.1 with hAdef
  have hzA : g₀.base m ∈ A := ⟨hzO₀, (hO hz).2⟩
  obtain ⟨h, hhle, hzD⟩ := hA.exists_basicOpen_le (V := A ⊓ O) ⟨g₀.base m, hzA, hz⟩ hzA
  set D := Z'.basicOpen h
  have hDA : D ≤ A := hhle.trans inf_le_left
  have hDO : D ≤ O := hhle.trans inf_le_right
  have htop : ⊤ ≤ g₀ ⁻¹ᵁ D := top_le_of_mem g₀ D hzD
  let δ : Γ(Z', D) →+ S := AddMonoidHom.mk' (Δ D) (hadd D hDO htop)
  have hδ : ∀ a, δ a = Δ D a := fun _ => rfl
  have h1 : Δ D 1 = 0 := by
    have e := hmul D hDO htop 1 1
    rw [_root_.mul_one, valR_one_of_le g₀ D htop, _root_.one_mul] at e
    have : Δ D 1 + Δ D 1 - Δ D 1 = Δ D 1 - Δ D 1 := by rw [← e]
    simpa using this
  have hgen : ∀ a : Γ(Z', A), Δ D (resG Z' hDA a) = 0 := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (φ.appLE O₀ A inf_le_left).hom ∪
        Set.range (p'.appLE U'.1 A inf_le_right).hom) := by rw [hcl]; trivial
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨f₀, rfl⟩ | ⟨r, rfl⟩
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hφ O₀ D _ hO₀W hDO htop f₀
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hp' D _ hDO htop r
    | zero => rw [map_zero, ← hδ, map_zero]
    | one => rw [map_one, h1]
    | add x y _ _ hx hy => rw [map_add, hadd D hDO htop, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, ← hδ, map_neg, hδ, hx, neg_zero]
    | mul x y _ _ hx hy => rw [map_mul, hmul D hDO htop, hx, hy, mul_zero, mul_zero, add_zero]
  have hall : ∀ b : Γ(Z', D), Δ D b = 0 := by
    intro b
    obtain ⟨u, r, hu, hb⟩ := GlobalTheory.LogKSLoc.exists_frac ⟨A, hA⟩ ⟨D, hA.basicOpen h⟩ hDA h rfl b
    have e := hmul D hDO htop b (resG Z' hDA u)
    have e2 : Δ D (b * resG Z' hDA u) = 0 := by
      have : b * resG Z' hDA u = resG Z' hDA r := hb
      rw [this, hgen]
    rw [e2, hgen, mul_zero, zero_add] at e
    have hunit : IsUnit (valR g₀ D (resG Z' hDA u)) := by
      obtain ⟨w, hw⟩ := hu
      refine IsUnit.of_mul_eq_one (valR g₀ D (w⁻¹ : (Γ(Z', D))ˣ)) ?_
      rw [← hw, ← GlobalTheory.CechKSSmul.valR_mul_of_le g₀ D htop, Units.mul_inv, valR_one_of_le g₀ D htop]
    exact (hunit.mul_right_eq_zero).mp e.symm
  rw [← hres O D hDO le_rfl htop f]
  exact hall _

end GlobalTheory.KSBaseChangeLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  first | exact @GlobalTheory.SecQuot.valR_secM_eq_mul_pow | exact GlobalTheory.SecQuot.valR_secM_eq_mul_pow | (intros; apply GlobalTheory.SecQuot.valR_secM_eq_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_fractionField_comm_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenericVal.valR_generic | exact GlobalTheory.GenericVal.valR_generic | (intros; apply GlobalTheory.GenericVal.valR_generic <;> assumption)
end

