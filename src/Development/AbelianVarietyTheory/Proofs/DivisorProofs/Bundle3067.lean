import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.TermsMove

theorem tors_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {g : GtPtF D F} {n : ℕ} (d : ℕ) (h : ∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) :
    ∃ o, GtPtF.IsNsmul (n * d) g o ∧ o.IsZero := by
  letI := @TorusExt.gtGroup
  obtain ⟨o, o₁, o₂⟩ := h
  rw [TorusExt.isNsmul_iff_eq] at o₁
  rw [TorusExt.isZero_iff_eq] at o₂
  refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
  rw [mul_nsmul, ← o₁, o₂, nsmul_zero]

theorem frExt_isGen {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {E : Type} (F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} (he : e.IsGen) : (frExt F e).IsGen :=
  pullGen_isGen A.L _ _ e he (TorsionExt.fieldMap (R := R) E F).left

open GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull in
set_option maxHeartbeats 800000 in

theorem exists_witnesses : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab x fr th w₀ s g' w h1 h2 h3 h4 h5 h6
    V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen x₂ fr₂ h1' h2' ρ hρ
  have hG := GlobalTheory.globalFns_holds
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  haveI : IsScalarTower (FractionRing V) (FractionRing V) (FractionRing V') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hF : Compat io (FractionRing V') := hf
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := map_maximalIdeal_le io
  have hg₂ : jFK (R := V') (FractionRing V') ≫ spMap f = jFK (R := V) (FractionRing V') := (Spec.map_comp _ _).symm
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w₀₂, hw₀₂, Ω, hΩ₁, hΩ₂, hE⟩ := exists_expand hG hmon hU hF hg₂ hcart.1 hwψ hgen h4 hκ
  obtain ⟨t', s', E', ht', hs'⟩ := (hE 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing V') 𝔪.U.toUnifPre hG h5)
  have hx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = (fieldMap (R := V) (FractionRing V) (FractionRing V') ≫ x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · show _ = (spMap f ≫ (x b).left) ≫ 𝔪.φ
      rw [Category.assoc, ← hφ, ← Category.assoc, h1', Category.assoc, 𝔗.lam_pt, Category.assoc, h1, ← Category.assoc,
        ← Category.assoc, ← spMap_comp, ← spMap_comp, hyK]
    · rw [Category.assoc, hcart.1.w, ← Category.assoc, Over.w, Over.w]
      exact hg₂
  have hfr : ∀ b, FrUp wψ (fr₂ (𝔗.lam b)) (frExt (FractionRing V') (fr b)) (ρ b : FractionRing V') := fun b z J J' hJ hJ' => by
    have e : vS (frExt (FractionRing V') (fr b)) z J = val (fr b) (spMap f) z J :=
      (val_frExt (fr b) (𝟙 _) hJ).trans (congrArg (fun q => val (fr b) q z J) (Category.id_comp _))
    rw [e]
    exact hρ b z J J' hJ hJ'
  have hv : ∀ b, ValAt t' (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b))
      (f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) * ((ρ b)⁻¹ ^ 1).val) := fun b =>
    valAt_pull hΩ₁ hΩ₂ ht' (hx b) (hfr b) (valAt_ext (h3 b))
  have t0 : (show AbSec 𝔪₂.A (FractionRing V') 1 from t') ≠ 0 := fun e => by
    have h₀ := hv x₀
    rw [show t' = (0 : AbSec 𝔪₂.A (FractionRing V') 1) from e] at h₀
    exact mul_ne_zero ((map_ne_zero f).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv))
      (Units.ne_zero _) (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨x', fr', Θ, -, k1, k2, k3, -⟩ := IntTerm.exists_points_frames_theta _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m _ δ 𝔪₂
  obtain rfl : x' = x₂ := funext fun a => Over.OverMorphism.ext (𝔪₂.cart.1.hom_ext ((k1 a).trans (h1' a).symm)
    ((Over.w _).trans (Over.w _).symm))
  have hΘ : ∀ a, ValAt Θ (x' a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩) := fun a z J' hJ' => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' 𝔗.X₂.ρ.P.isLB z
    have e := mul_left_cancel (((k2 a).2 z J J' hJ hJ').trans ((h2' a).2 z J J' hJ hJ').symm)
    have b := k3 a z J' hJ'
    rw [FrameMove.val_powFrame] at b ⊢
    rwa [← e]
  obtain ⟨K, hK⟩ := exists_eq_smul t0 Θ
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') le_rfl w₀₂ hw₀₂
  choose g₁ w₁ a₁ a₂ a₃ a₄ using fun c => exists_ext (F := FractionRing V') hG 𝔪.U h4 (g' c) (h6 c).2.1
  choose g₂ w₂ b₁ b₂ b₃ b₄ using fun c => exists_point hG hI hF hκ hΩ₁ hΩ₂ (fun k hk => (hE k hk).2) (g₁ c) (a₁ c) (ρ (lab c))
  refine ⟨Θ, w₀₂, K • s', g₂, w₂, K, hΘ, hw₀₂, (he' _ _).2 ?_, fun c => ⟨?_, b₁ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e' hK).trans ((map_smul e' K _).trans (congrArg (K • ·) ((he' _ _).1 E')))
  · rw [𝔗.lev]
    exact tors_mul _ (b₂ c _ (a₂ c _ (h6 c).1))
  · exact b₄ c (x' (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c))) _ (frExt (FractionRing V') (fr (lab c)))
      (frExt_isGen _ (h2 (lab c)).1) (hx (lab c)) (hfr (lab c)) (a₄ c (x (lab c)) (fr (lab c)) (h2 (lab c)).1 (h6 c).2.2)
  · rw [coef_smul (b₁ c), _root_.mul_assoc, b₃ c _ _ hs', a₃, he₈]
    rfl
  · have h₀ := valAt_lin (hv b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at h₀
    rw [valAt_unique (hΘ _) h₀, pow_one, _root_.mul_assoc, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end GlobalTheory.TermsMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivariStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_finiteExtension_galoisEquivariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  first | exact @GlobalTheory.Mum.exists_labels_finExt_galEqN | exact GlobalTheory.Mum.exists_labels_finExt_galEqN | (intros; apply GlobalTheory.Mum.exists_labels_finExt_galEqN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_pair_of_torsion_point_over : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  first | exact @GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_spread_over_trait_specialisation : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | exact GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_spread₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.GraphPlace

section Gen

variable {K L F W : Type} [Field K] [Field L] [Field F] [Field W] [Algebra K L] [Algebra K F] [Algebra L W]
  [Algebra K W] [IsScalarTower K L W]

omit [Algebra K W] [IsScalarTower K L W] in

theorem indep_of_lift {ι : Type} (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) {x : ι → F}
    (hx : AlgebraicIndependent K x) : AlgebraicIndependent L fun i => ψ (1 ⊗ₜ x i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) (MvPolynomial.aeval (R := K) x).toLinearMap
      (algebraicIndependent_iff_injective_aeval.1 hx)
  have e : (MvPolynomial.aeval (R := L) fun i => ψ (1 ⊗ₜ x i)) =
      (ψ.comp (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x))).comp
        (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.toAlgHom := by
    ext i
    simp
  rw [e]
  exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.injective

theorem trdeg_of_lift (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) (M : IntermediateField L W)
    (h1 : ∀ f, ψ (1 ⊗ₜ f) ∈ M) (h2 : M ≤ IntermediateField.adjoin L (Set.range fun f => ψ (1 ⊗ₜ f))) :
    Algebra.trdeg L M = Algebra.trdeg K F := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K F
  have hy := indep_of_lift ψ hψ hx.1
  rw [← hx.cardinalMk_eq_trdeg]
  apply le_antisymm
  · let E := IntermediateField.adjoin L (Set.range fun i => ψ (1 ⊗ₜ x i))
    let A := (algebraicClosure E W).restrictScalars L
    have hA : M ≤ A := by
      refine h2.trans (IntermediateField.adjoin_le_iff.2 ?_)
      rintro _ ⟨f, rfl⟩
      show ψ (1 ⊗ₜ f) ∈ algebraicClosure E W
      rw [mem_algebraicClosure_iff]
      let φ : F →ₐ[K] W := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
      have hf : IsAlgebraic (Algebra.adjoin K (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
      have hm : ∀ a ∈ Algebra.adjoin K (Set.range x), φ a ∈ E := by
        intro a ha
        have : Algebra.adjoin K (Set.range x) ≤ ((E.restrictScalars K).toSubalgebra).comap φ := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨i, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        exact this ha
      let g : Algebra.adjoin K (Set.range x) →+* E :=
        (φ.toRingHom.comp (Algebra.adjoin K (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
      have hg : Function.Injective g := fun a b h =>
        Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val h))
      exact hf.ringHom_of_comp_eq g φ.toRingHom hg rfl
    have hE : Algebra.trdeg L E ≤ Cardinal.mk ι := by
      have : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
        rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
        have htop : IntermediateField.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
          apply IntermediateField.lift_injective
          rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
          rfl
        rw [htop]
        infer_instance
      exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk L _ (alg := this)).trans Cardinal.mk_range_le
    calc Algebra.trdeg L M ≤ Algebra.trdeg L A :=
          trdeg_le_of_injective (IntermediateField.inclusion hA) (IntermediateField.inclusion_injective hA)
      _ = Algebra.trdeg L (algebraicClosure E W) := rfl
      _ = Algebra.trdeg L E := by
          haveI : FaithfulSMul E (algebraicClosure E W) :=
            (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E (algebraicClosure E W)).injective
          rw [← trdeg_add_eq L E (A := algebraicClosure E W), trdeg_eq_zero (R := E) (A := algebraicClosure E W), add_zero]
      _ ≤ _ := hE
  · have : AlgebraicIndependent L fun i => (⟨ψ (1 ⊗ₜ x i), h1 _⟩ : M) :=
      AlgebraicIndependent.of_comp M.val hy
    exact this.cardinalMk_le_trdeg

end Gen

theorem exists_trBasis {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
    [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
    [IsFractionRing (K ⊗[ℂ] κ') L] {n k' : ℕ} {x : Fin n → K} {τ' : Fin k' → κ'}
    (hx : TrBasis (algebraMap ℂ K) x) (hτ : TrBasis (algebraMap ℂ κ') τ') :
    ∃ w : Fin (k' + n) → L, TrBasis (algebraMap ℂ L) w := by
  have e1 : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e2 : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e3 : (algebraMap ℂ L).toAlgebra = (inferInstance : Algebra ℂ L) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at *
  rw [e1] at hx
  rw [e2] at hτ
  rw [e3]
  letI : Algebra K L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap K (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower K (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L,
      IsScalarTower.algebraMap_apply ℂ K (K ⊗[ℂ] κ')]
    rfl
  have h1 : Algebra.trdeg K L = Algebra.trdeg ℂ κ' := by
    let ψ := IsScalarTower.toAlgHom K (K ⊗[ℂ] κ') L
    rw [← trdeg_of_lift ψ (IsFractionRing.injective _ _) ⊤ (fun _ => trivial) ?_]
    · exact (IntermediateField.topEquiv (F := K) (E := L)).trdeg_eq.symm
    · intro z _
      have hm : ∀ a, ψ a ∈ IntermediateField.adjoin K (Set.range fun f => ψ (1 ⊗ₜ f)) := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem _
        | add a b ha hb => rw [map_add]; exact add_mem ha hb
        | tmul l f =>
          have : l ⊗ₜ[ℂ] f = l • ((1 : K) ⊗ₜ[ℂ] f) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul]
          exact IntermediateField.smul_mem _
            (IntermediateField.subset_adjoin K _ (Set.mem_range_self f))
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') z
      exact div_mem (hm a) (hm b)
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K L).injective
  have h2 := trdeg_add_eq ℂ K (A := L)
  rw [h1, ← hx.cardinalMk_eq_trdeg, ← hτ.cardinalMk_eq_trdeg] at h2
  obtain ⟨ι, w, hw⟩ := exists_isTranscendenceBasis' ℂ L
  have h3 : Cardinal.mk (Fin (k' + n)) = Cardinal.mk ι := by
    rw [hw.cardinalMk_eq_trdeg, ← h2]
    simp [add_comm]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  exact ⟨w ∘ e, hw.comp_equiv e⟩

theorem exists_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  IsLocModel (algebraMap ℂ K) R → Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ g : K, algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    V.formOrd (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hπ hR hinj hfr M hk _
  obtain ⟨Q, hQ, z, hm, hdim, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.localRing_graph_generic_point_of_injective (L := L) n k k' x τ' R π ρ hx hτ hz hc hπ hinj hfr hR hO hk
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := exists_trBasis (L := L) hx hτ
  obtain ⟨V, hV, hunit, -, hpow, hfo⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ r (k' + n) z (fun _ => 1)
    hm (by rw [hdim]; push_cast; rfl) rfl (fun _ => le_rfl) ⟨w, hw⟩
  have hne : ∀ q : Q, IsUnit q → (q : L) ≠ 0 := fun q hq => (hq.map Q.subtype).ne_zero
  refine ⟨V, fun g => ?_, fun b h => ?_, fun g h => ?_, fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · by_cases h : g = 0
    · subst h
      rw [TensorProduct.zero_tmul, map_zero]
      exact zero_mem _
    · obtain ⟨q, -, e⟩ := hg g h
      exact e ▸ hV _ q.2
  · obtain ⟨q, hq, e⟩ := hb b h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hg g h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hu l a b h
    exact e ▸ ⟨hne q hq, hunit q hq⟩
  · obtain ⟨q, e, hq⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    exact hpow M q h0 hq
  · have h := hfo y hy
    have hs : V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) =
        V.formOrd (dForm (algebraMap ℂ L) (fun i => (y i : L))) := by
      by_cases h0 : dForm (algebraMap ℂ L) (fun i => (y i : L)) = 0
      · rw [h0, smul_zero]
      · rw [V.formOrd_smul hw h0 (hne q hq), hunit q hq, zero_add]
    rw [hform, hs]
    simpa using h

end GlobalTheory.FieldPair.GraphPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmall
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef.BoxTwist

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_shift_tens (N M : HermLB p) (u : ℝ) :
    ((N.tens M).shift (fun _ => u) fun _ => rfl).Isometric (N.tens (M.shift (fun _ => u) fun _ => rfl)) :=
  HermLB.isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => (add_assoc _ _ _).symm

variable [IsIntegral X]

theorem isRatSec_const_mul {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (g : X.functionFieldˣ) :
    IsRatSec B fun i => g * r i := fun a b h => by
  beta_reduce
  rw [Units.val_mul, Units.val_mul, hr a b h]
  ring

theorem exists_pair_small (Q : Pair p) (W : HermLB p) (g : X.functionField) (hg : g ≠ 0) (u : ℝ) :
    ∃ P : Pair p, P.L = W ∧ P.A = Q.A.shift (fun _ => u) (fun _ => rfl) ∧
      ∀ f, g * f ∈ Q.Bl 0 1 (Real.exp u) → f ∈ P.Bl 0 1 1 := by
  obtain ⟨r, hr⟩ := exists_isRatSec W.isLB
  let P : Pair p := ⟨W, Q.A.shift (fun _ => u) (fun _ => rfl), r, fun j => Units.mk0 g hg * Q.r' j, hr,
    isRatSec_const_mul Q.hr' _⟩
  have e (f i i' j) : P.loc 0 1 f i j = Q.loc 0 1 (g * f) i' j := by
    simp only [Pair.loc, P, zpow_zero, zpow_one, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨P, rfl, rfl, fun f hf => ⟨fun x i j _ hj => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨i', hi'⟩ := exists_chart Q.L.isLB x
    rw [e f i i' j]
    exact hf.1 x i' j hi' hj
  · have h := hf.2 σ y
    have e' : P.nu 0 1 σ y f = Q.nu 0 1 σ y (g * f) * Real.exp (-u) := by
      rw [Pair.nu, Pair.nu, e f _ (pick (Q.L.φ σ).isLB y), mul_assoc, ← Real.exp_add]
      congr 2
      have : (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y = (Q.A.φ σ).φ (pick (Q.A.φ σ).isLB y) y + 2 * u := rfl
      rw [this]
      push_cast
      ring
    rw [e']
    calc _ ≤ Real.exp u * Real.exp (-u) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem exists_twist : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  intro hC k _ X _ p D hX N x
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair N A
  obtain ⟨c, g, -, hg, -, hgf⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P hA (-1) (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  choose v hv0 hv using fun S => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P (-1) c _ (hgf S)
  let u : ℝ := ∑ S, v S
  have hu : 0 ≤ u := Finset.sum_nonneg fun S _ => hv0 S
  have hvu (S) : v S ≤ u := Finset.single_le_sum (fun S _ => hv0 S) (Finset.mem_univ S)
  let M : HermLB p := P.L.dual.tens (P.A.pow c)
  obtain ⟨h₁, h₂, -⟩ := Pair.rep_base k X p P
  have hM : P.Rep (-1) c M := by
    simpa using Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_dual k X p P _ _ _ h₁) (Pair.rep_pow k X p P _ _ _ c h₂)
  obtain ⟨Q, -, hQ, hB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P _ _ _ _ M M hM hM
  have hi : (P.A.pow c).Isometric (P.L.tens M) :=
    HermLB.icls_eq_iff.1 (by simp only [M, HermLB.icls_tens, HermLB.icls_dual]; abel)
  have hn : (P.L.tens M).IsNef D :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ hi).2.1 (GlobalTheory.NefPow.isNef_pow hC k X p D hX _ c hAn)
  refine ⟨M.shift (fun _ => u) fun _ => rfl, (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ (isometric_shift_tens _ _ u)).2.1
    (GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX _ u hu hn), fun W => ?_⟩
  obtain ⟨R, hR, hR', h⟩ := exists_pair_small Q W g hg u
  refine ⟨R, hR, by rw [hR', hQ], fun S => h _ ?_⟩
  rw [hB]
  simp only [zero_mul, one_mul, zero_add]
  exact ⟨(hv S).1, fun σ y => ((hv S).2 σ y).trans (Real.exp_le_exp.2 (hvu S))⟩

end GlobalTheory.HSNef.BoxTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  first | exact @GlobalTheory.Mum.exists_galMap | exact GlobalTheory.Mum.exists_galMap | (intros; apply GlobalTheory.Mum.exists_galMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldLiftsAffineCoverSmoothGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_lifts_affine_cover_smooth_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := by
  first | exact @GlobalTheory.KSLift.exists_lifts | exact GlobalTheory.KSLift.exists_lifts | (intros; apply GlobalTheory.KSLift.exists_lifts <;> assumption)
end

