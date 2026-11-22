import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModule
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem one_left {X' : Scheme.{0}} {G : Over X'} [GrpObj G] {Y : Scheme.{0}} (t : Y ⟶ X') :
    (1 : Over.mk t ⟶ G).left = t ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.TorsSpec

namespace GlobalTheory.EqvAct

open GlobalTheory.TorsSpec in

theorem torsLevel_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ I g _ hMb Γ _ _ ι ρ _ X' _ φ ℓ ρ' hX _ hℓo hℓ hρ m hm hmv
  haveI := hX
  haveI := hℓo
  have hsemi : IsSemiAbelian (pullG TF Z φ) := IsSemiAbelian.pullback _ _ TF.Y.t.semi
  haveI := hsemi.smooth
  haveI := hsemi.separated
  haveI := hsemi.comm
  haveI : Nonempty (V₀ TF.Y Z) := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨⟨z, (j_mem_barComp Z z).2 hz⟩⟩
  have hn : IsUnit ((l.M : ℕ) : Γ(X', ⊤)) := by
    have h0 : IsUnit ((l.M : ℕ) : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by have := l.three_le; omega))
    have := h0.map (((φ ≫ s₀ TF.Y Z).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
    simpa using this
  have hnI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    have h0 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact hMb ((Ideal.mul_le_inf.trans inf_le_left) h0)
  have hmv' : ∀ γ x, etaSecL TF Z φ ℓ hℓ x ≫ m γ = (ρ γ).hom ≫ etaSecL TF Z φ ℓ hℓ (ι γ x) := by
    intro γ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (ι γ (Submodule.Quotient.mk b))
    rw [← ha]
    refine hmv γ a b ?_ _ _ (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_ψ TF Z φ ℓ hℓ b)
      (etaSecL_ψ TF Z φ ℓ hℓ a)
    rw [ha]
    exact ((ι γ).symm_apply_apply _).symm
  intro K _ _ t
  classical
  have hlift : ∀ P : Over.mk t ⟶ pullG TF Z φ, IsTorsI I (pullAct TF Z φ) P →
      ∃ PT : Sp K ⟶ (torsion (pullG TF Z φ) l.M).left, PT ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left ∧
        ∃ x, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT (IsLocalRing.closedPoint K)) x := by
    intro P hP
    have h1 : P ≫ mulN (pullG TF Z φ) l.M = 1 := by rw [← act_natCast (pullAct TF Z φ)]; exact hP _ hnI
    obtain ⟨PT, hPT⟩ := exists_lift_torsion l.M P h1
    have hPT' : PT.left ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left := by rw [← Over.comp_left, hPT]
    refine ⟨PT.left, hPT', GlobalTheory.T.exists_class_torsionPoint_localScheme (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ)
      (pullAct TF Z φ) I (GlobalTheory.T.exists_levelSection_of_ideal_torsion_at_geometricPoint TF Z φ ℓ hℓ I hMb) K PT.left (fun a ha => ?_) _⟩
    have e1 := congrArg Over.Hom.left (hP a ha)
    rw [Over.comp_left, one_left] at e1
    rw [reassoc_of% hPT', e1, ← Category.assoc, Over.w PT]
    rfl
  let PT : ∀ P, IsTorsI I (pullAct TF Z φ) P → (Sp K ⟶ (torsion (pullG TF Z φ) l.M).left) :=
    fun P h => Classical.choose (hlift P h)
  have hPT : ∀ P h, PT P h ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left :=
    fun P h => (Classical.choose_spec (hlift P h)).1
  let cl : ∀ P, IsTorsI I (pullAct TF Z φ) P → LevelMod Dw l :=
    fun P h => Classical.choose (Classical.choose_spec (hlift P h)).2
  have hcl : ∀ P h, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT P h (IsLocalRing.closedPoint K)) (cl P h) :=
    fun P h => Classical.choose_spec (Classical.choose_spec (hlift P h)).2
  have hun := GlobalTheory.T.levelSection_injective_at_geometricPoint TF Z φ ℓ hℓ
  refine ⟨fun P => if h : IsTorsI I (pullAct TF Z φ) P then cl P h else 0, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    have hPQ : IsTorsI I (pullAct TF Z φ) (P * Q) := fun a ha => by
      haveI := (pullAct TF Z φ).hom a
      rw [MonObj.mul_comp, hP a ha, hQ a ha, _root_.mul_one]
    simp only [dif_pos hP, dif_pos hQ, dif_pos hPQ]
    exact GlobalTheory.T.torsionPoint_class_mul_eq_add (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun
      (GlobalTheory.T.levelSection_add_at_geometricPoint TF Z φ ℓ hℓ) K t P Q _ _ _ (hPT P hP) (hPT Q hQ) (hPT _ hPQ) _ _ _ _ (hcl P hP) (hcl Q hQ)
      (hcl _ hPQ)
  · intro P a hP
    have hPa : IsTorsI I (pullAct TF Z φ) (P ≫ (pullAct TF Z φ).act a) := fun r hr => by
      rw [Category.assoc, ← (pullAct TF Z φ).mul]
      exact hP _ (I.mul_mem_left a hr)
    simp only [dif_pos hP, dif_pos hPa]
    exact GlobalTheory.T.torsionPointClassAtStalk_smul_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      (GlobalTheory.T.levelSection_smul_at_geometricPoint TF Z φ ℓ hℓ) K t P a _ _ (hPT P hP) (hPT _ hPa) _ _ _ (hcl P hP) (hcl _ hPa)
  · intro P Q hP hQ he
    simp only [dif_pos hP, dif_pos hQ] at he
    exact GlobalTheory.T.eq_of_torsionPointClassAtStalk_eq (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) K t P Q _ _
      (hPT P hP) (hPT Q hQ) _ _ (hcl P hP) (he ▸ hcl Q hQ)
  · intro γ ht P Q hP hQP
    have hQ : IsTorsI I (pullAct TF Z φ) Q := fun a ha => by
      refine Over.OverMorphism.ext ?_
      have e1 := congrArg Over.Hom.left (hP a ha)
      rw [one_left] at e1
      rw [Over.comp_left, one_left, hQP, Category.assoc, ← hm.2.1 γ a, ← Category.assoc, ← Over.comp_left, e1,
        Category.assoc, eta_comp_of_isGrpPullback (hm.1 γ), ← Category.assoc, ht]
    simp only [dif_pos hP, dif_pos hQ]
    exact GlobalTheory.T.torsionPoint_class_image_eq_level_action (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      ρ' ρ hρ ι m hm hmv' K t γ P Q _ _ (hPT P hP) (hPT Q hQ) hQP _ _ _ (hcl P hP) (hcl Q hQ)

end GlobalTheory.EqvAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TorsRatio

variable {V : Type} [CommRing V] [IsDomain V]

def cstK (z : (TFK (R := V) (FractionRing V)).left) :
    FractionRing V →+* (TFK (R := V) (FractionRing V)).left.presheaf.stalk z :=
  ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem cst_eq_cstK (z : (TFK (R := V) (FractionRing V)).left) (a : FractionRing V) :
    GlobalTheory.UT.cst (R := V) (FractionRing V) z a = cstK z a :=
  gs_eq (𝟙 _) z ⊤ trivial _

theorem pt_eq (z z' : (TFK (R := V) (FractionRing V)).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) z z'

theorem cstK_surj (z : (TFK (R := V) (FractionRing V)).left) : Function.Surjective (cstK (V := V) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TFK (R := V) (FractionRing V)).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 s
  exact ⟨x, congrArg ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom hx⟩

theorem frame_ratio {A : PolAV (Sp (FractionRing V))} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (he : e.IsGen) (he' : e'.IsGen) : ∃ l : FractionRing V, l ≠ 0 ∧ ∀ z J, Good A.L z J →
      (Geo.Tor.val e' (𝟙 _) z J).val = cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J' hJ' using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ' : Good A.L z J' := hJ'
  obtain ⟨l, hl⟩ := cstK_surj z (Geo.Tor.val e' (𝟙 _) z J' * (Geo.Tor.val e (𝟙 _) z J')⁻¹).val
  refine ⟨l, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  · obtain rfl := pt_eq z z'
    have t₁ : Geo.Tor.val e (𝟙 _) z J = _ * Geo.Tor.val e (𝟙 _) z J' :=
      gen_trans he (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have t₂ : Geo.Tor.val e' (𝟙 _) z J = _ * Geo.Tor.val e' (𝟙 _) z J' :=
      gen_trans he' (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    rw [hl, t₁, t₂, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.Poinc.TorsRatio

namespace GlobalTheory.Poinc.TorsRatio

theorem valAt_torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V)))
    (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N →
    ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' →
    ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c →
      ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  intro V _ _ A ρA _ N _ x e e' H H' th c hv
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'

  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  refine ⟨l⁻¹, by rw [inv_pow, hlN, inv_one], fun z' J' hJ' => ?_⟩
  rw [hv z' J' hJ']
  have r₁ : Geo.Tor.val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z' J' = Geo.Tor.val e (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) :=
    map_zpow _ _ _
  have r₂ : Geo.Tor.val (powFrame A.A A.L x e' ((1 : ℕ) : ℤ)) (𝟙 _) z' J' =
      Geo.Tor.val e' (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) := map_zpow _ _ _
  rw [r₁, r₂, Nat.cast_one, zpow_one, zpow_one, hl z' J' hJ']
  simp only [id, cst_eq_cstK]
  rw [← _root_.mul_assoc, ← map_mul, mul_comm l⁻¹ c, inv_mul_cancel_right₀ hl0]

end GlobalTheory.Poinc.TorsRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Labels

theorem eq_comp_of_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegData R (maximalIdeal R)}
    {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G)
    (π : A'.A ⟶ A.A) (h : (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ π) {T : Over (Sp (FractionRing R))}
    (a : T ⟶ A.A) (a' : T ⟶ A'.A) (e : a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left) : a = a' ≫ π := by
  have hU := GlobalTheory.TauFormHom.isGrpPullback_genMap U
  have h' : U'.gen.inv ≫ (Over.pullback (jK R)).map p = π ≫ U.gen.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : π.left ≫ U.gen.inv.left = U'.gen.inv.left ≫ ((Over.pullback (jK R)).map p).left := by
    rw [← Over.comp_left, ← Over.comp_left, h']
  have hf : ((Over.pullback (jK R)).map p).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ p.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  refine hU.1.hom_ext ?_ ?_
  · rw [e, Over.comp_left, genMap, genMap]
    simp only [Category.assoc]
    rw [reassoc_of% h'', hf]
  · rw [Over.w a, Over.w (a' ≫ π)]

theorem commutatorPairing_eighthPower_bundle : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P P' : PolAV S) (pr : Fin 8 → (P'.A ⟶ P.A)), (∀ a, IsMonHom (pr a)) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), LBIso P'.L (LB.LinComb (abelian₂ P.A P.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (n : ℕ) (T : Over S) (x y : T ⟶ P'.A), x ^ n = 1 → y ^ n = 1 → ∀ (c : Fin 8 → Fin 8 → Γ(T.left, ⊤)ˣ), (∀ a b, WeilIs P.A P.L n (x ≫ pr a) (y ≫ pr b) (c a b)) → WeilIs P'.A P'.L n x y (∏ ab : Fin 8 × Fin 8, (c ab.1 ab.2 * c ab.2 ab.1) ^ W ab.1 ab.2) := by
  intro S _ P P' pr hpr W hL n T x y hx hy c hc
  have hG := GlobalTheory.globalFns_holds
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hM := LB.isLB_linComb hΛ (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hφ : ∀ ab : Fin 8 × Fin 8, IsMonHom (lift (pr ab.1) (pr ab.2)) := fun ab => by
    haveI := hpr ab.1
    haveI := hpr ab.2
    infer_instance
  have ht : ∀ {z : T ⟶ P'.A}, z ^ n = 1 → ∀ a, (z ≫ pr a) ^ n = 1 := fun {z} hz a => by
    haveI := hpr a
    rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have key := GlobalTheory.PairingComb.weilIs_linComb hG P'.isAb hΛ (fun ab : Fin 8 × Fin 8 => lift (pr ab.1) (pr ab.2)) hφ
    (fun ab => W ab.1 ab.2) (n := n) (x := x) (y := y) (fun ab => c ab.1 ab.2 * c ab.2 ab.1) (fun ab => by
      rw [comp_lift, comp_lift]
      exact GlobalTheory.T.weilPairing_mumfordLambda_square S P n T _ _ _ _ (ht hx _) (ht hx _) (ht hy _) (ht hy _) _ _ (hc ab.1 ab.2) (hc ab.2 ab.1))
  refine GlobalTheory.PELFamily.weilIs_of_lbIso hG P'.isAb P'.isLB hM ?_ key
  refine LBIso.trans P'.isLB hM (pull_isLB hM _) hL ?_
  have := GlobalTheory.DescendedPrincipal.lbIso_pull_id hM
  simpa using this.symm

theorem sum_symmetrised_bilinear_matrix_eq {J X Y : Type} [Fintype J] [AddCommGroup X] [AddCommGroup Y] (W : Matrix J J ℤ) (c : J → (X →+ Y))
    (l : J → X) :
    ∑ ab : J × J, W ab.1 ab.2 • (c ab.1 (l ab.2) + c ab.2 (l ab.1)) =
      ∑ u, c u (∑ w, (W + W.transpose) u w • l w) := by
  rw [Fintype.sum_prod_type]
  simp only [smul_add, Finset.sum_add_distrib, map_add, map_sum, map_zsmul, Matrix.add_apply, Matrix.transpose_apply,
    add_smul]
  congr 1
  exact Finset.sum_comm

theorem label_proj_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ v : Fin 8, (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ (pG v).left → ∃ z, q.y = e q'.y v + k • z) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e he v F _ _ _ k hk
    q q' a a' hqa hqa' hla
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkF : (k : F) ≠ 0 := by
    have h := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨f, ⟨i₁, s₁, q₁, -, w₁⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, -, -, -, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
  obtain rfl : a = f q := (i₁ q a).1 hqa
  obtain rfl : a' = f' q' := (i₂ q' a').1 hqa'
  have hav : f q = f' q' ≫ pr v := eq_comp_of_genMap U U' (pG v) (pr v) (hgen v) _ _ hla
  have hpw : ∀ w, (f' q' ≫ pr w) ^ k = 1 := fun w => by
    haveI := hpr w
    rw [← MonObj.pow_comp, p₂, MonObj.one_comp]
  choose qw hqw using fun w => s₁ _ (hpw w)
  have key : ∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ k = 1 →
      τ (Multiplicative.ofAdd (q.y - e q'.y v)) = 1 := by
    intro τ hτ
    have hτk : ∀ x, τ x ^ k = 1 := fun x => by
      rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    let ev : D'.toPre.X →+ D.toPre.X := (Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom
    let τ' : Multiplicative D'.toPre.X →* Fˣ := τ.comp (AddMonoidHom.toMultiplicative ev)
    have hτ' : τ' ^ k = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    let τu : Fin 8 → (Multiplicative D.toPre.X →* Fˣ) := fun u => τ'.comp (AddMonoidHom.toMultiplicative (c u))
    have hτu : ∀ u, τu u ^ k = 1 := fun u => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    obtain ⟨tT', htT'y, htT'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB' τ' hτ'
    choose tT htTy htT using fun u => GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB (τu u) (hτu u)
    have hproj : ∀ u, f (tT u) = f' tT' ≫ pr u := fun u =>
      eq_comp_of_genMap U U' (pG u) (pr u) (hgen u) _ _
        (hc u F (fun _ => rfl) k hk (τu u) τ' (tT u) tT' (f (tT u)) (f' tT') hτ' (fun _ => rfl) (htTy u) (htT u)
          htT'y htT' ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl))
    have hA : ∀ u w, WeilIs A.A A.L k (f' tT' ≫ pr u) (f' q' ≫ pr w)
        (unitOn (τ' (Multiplicative.ofAdd (c u (qw w).y)))) := fun u w => by
      rw [← hproj u, ← hqw w]
      exact (w₁ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns (tT u) (qw w) (htTy u) (htT u))
    have hA' : WeilIs A'.A A'.L k (f' tT') (f' q') (unitOn (τ' (Multiplicative.ofAdd q'.y))) :=
      (w₂ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns tT' q' htT'y htT')
    have hA₂ := commutatorPairing_eighthPower_bundle _ A A' pr hpr W hL k _ (f' tT') (f' q') (p₂ _) (p₂ _) _ hA
    have hval : (∏ ab : Fin 8 × Fin 8, (unitOn (τ' (Multiplicative.ofAdd (c ab.1 (qw ab.2).y))) *
        unitOn (τ' (Multiplicative.ofAdd (c ab.2 (qw ab.1).y)))) ^ W ab.1 ab.2) =
        unitOn (τ' (Multiplicative.ofAdd (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)))) := by
      let ψ : Multiplicative D'.toPre.X →* Γ(Sp F, ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom).comp τ'
      have hψ : ∀ x, unitOn (τ' x) = ψ x := fun x => rfl
      simp only [hψ]
      rw [← sum_symmetrised_bilinear_matrix_eq W c (fun w => (qw w).y), ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun ab _ => ?_
      rw [ofAdd_zsmul, map_zpow, ofAdd_add, map_mul]
    rw [hval] at hA₂
    have hu := GlobalTheory.weilIs_unique_fieldPoint _ A'.A A'.L A'.isLB F _ k _ _ _ _ hA' hA₂
    have hinv : e (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)) = fun w => (qw w).y := by
      have := he (e.symm fun w => (qw w).y)
      rw [e.apply_symm_apply] at this
      rw [this, e.apply_symm_apply]
    have h₁ : τ (Multiplicative.ofAdd (e q'.y v)) = τ (Multiplicative.ofAdd (qw v).y) := by
      have := hu
      simp only [τ', ev, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
        AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom, hinv] at this
      exact this
    obtain ⟨z, hz, -⟩ := (q₁ (qw v) q).1 (by rw [hqw, hav])
    rw [ofAdd_sub, map_div, h₁, hz, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, hτk, _root_.mul_one, div_self']
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one _ F k hkF _ key
  exact ⟨z, by rw [← hz]; abel⟩

end GlobalTheory.Poinc.Eq8.Labels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsPullbackUniformisationCommonField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.Sep.BaseChangeLabels

theorem qkToAkU_pullback_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  intro V V' _ _ _ _ _ _ hV hV' j hj _ D A G _ _ _ U D' hD A' gA U' hPU hgU hgA F' _ _ _ hF k hk p₁ x₁ hQ

  have hcomp : algebraMap (FractionRing V) F' = (algebraMap (FractionRing V') F').comp (fracMap hj) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext r
    simp only [RingHom.comp_apply, fracMap_algebraMap]
    exact hF r

  have P := GlobalTheory.UT.EndBaseChange.points GlobalTheory.firstFiveLaws.1.globalFns hD D.tau_bimult D'.tau_bimult F' hF
  obtain ⟨g', hg', -⟩ := P.1 p₁.g
  obtain ⟨h, hn, hi⟩ := p₁.eq
  obtain ⟨h', hh', -⟩ := P.1 h
  have hn' := (P.2.2.2 k p₁.g g' h h' hg' hh').1 hn
  have hi' : GtPtF.IsIota (hD.xe.symm p₁.y) h' := (P.2.2.1 h h' (hD.xe.symm p₁.y) hh').1 (by simpa using hi)
  let p' : QkPt D'.toPre F' k := ⟨hD.xe.symm p₁.y, g', ⟨h', hn', hi'⟩⟩

  have sq : x₁.left ≫ A.A.hom = (TFK (R := V') F').hom ≫ spMap (fracMap hj) := by
    rw [Over.w x₁]
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F')) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V') F')) ≫ Spec.map (CommRingCat.ofHom (fracMap hj))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let l := hgU.1.lift x₁.left (TFK (R := V') F').hom sq
  have hl₁ : l ≫ gA = x₁.left := hgU.1.lift_fst _ _ sq
  have hl₂ : l ≫ A'.A.hom = (TFK (R := V') F').hom := hgU.1.lift_snd _ _ sq
  let x' : TFK (R := V') F' ⟶ A'.A := Over.homMk l hl₂
  have hx' : x'.left ≫ gA = x₁.left := hl₁

  have hA : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hA' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf j)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  refine ⟨p', x', rfl, ?_, hx'⟩
  refine GlobalTheory.firstFiveLaws.2.2.2.2.qkBaseChange V V' (maximalIdeal V) (maximalIdeal V') hA hA' j D A G U
    ((Over.pullback (specOf j)).obj G) (Iso.refl _) mR A' D' hD U' hPU F' hF k hk p₁ x₁ p' x' rfl hg' ?_ hQ
  rw [Iso.refl_hom, Over.id_left, Category.id_comp, ← hx', Category.assoc, hgA]

end GlobalTheory.Poinc.Sep.BaseChangeLabels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsion_isLev : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  intro X g n B _ ζ sX c hζ S A _ y α hα F _ _ t x hx
  let β : B →+* F := (Spec.preimage ((t ≫ y) ≫ sX)).hom
  obtain ⟨-, hs, -⟩ := c.geom F (t ≫ y) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hx₁ : pushHom hα (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨a, ha⟩ := hs _ hx₁
  have hu : (toUnit (Over.mk (t ≫ y))).left = t ≫ y := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (t ≫ y) ≫ (c.lev a).left = x.left ≫ α := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  exact ⟨a, by rw [← e, Category.assoc]⟩

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinates_compare_normalisedGenerators : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  first | exact @GlobalTheory.Mum.Two.coord_of_lin | exact GlobalTheory.Mum.Two.coord_of_lin | (intros; apply GlobalTheory.Mum.Two.coord_of_lin <;> assumption)
end

