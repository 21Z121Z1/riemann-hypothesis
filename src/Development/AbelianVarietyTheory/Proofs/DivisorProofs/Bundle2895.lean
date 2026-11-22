import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormQuotientClassEqOfRelDifferences
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

open GlobalTheory.CechPic GlobalTheory.Poinc.GalTrans

theorem exists_twist_along_genericAutomorphism {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S S' : ThetaSys o Ω} (ρ : S.Real)
    (ρ' : S'.Real) (l' : S.Gam → S'.Gam) (h' : USame ρ ρ' l' (RingHom.id _)) (σ τ : Ω →+* Ω)
    (hτ : τ.comp σ = RingHom.id _) (hσ : σ.comp τ = RingHom.id _) (a : S.Gam → S.Gam)
    (P₀ : PolAV (Sp Ω)) (b : P₀.A.left ⟶ ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (hb : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) b)
    (ht : IsGrpPullback P₀.A P₀.A (spMap σ) t) (lb : LBIso P₀.L (ρ.P.L.pull b)) (lt : LBIso P₀.L (P₀.L.pull t))
    (hp : ∀ x (w w' : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left)
    {B : Scheme.{0}} {v : Sp Ω ⟶ B} {r : B ⟶ Sp S'.R} (hv : v ≫ r = spMap S'.R.val.toRingHom)
    (G : Over B) [GrpObj G] (α : G.left ⟶ ρ'.P.A.left) (hα : IsGrpPullback G ρ'.P.A r α)
    {Y : Scheme.{0}} (N : LB Y) (hN : N.IsLB) (β : G.left ⟶ Y) (hL : LBIso (ρ'.P.L.pull α) (N.pull β)) :
    ∃ (P₁ : PolAV (Sp Ω)) (e : P₁.A.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ P₁.A.left) (k₀ : P₁.A.left ⟶ G.left),
      IsGrpPullback P₁.A P₀.A (spMap σ) e ∧ IsGrpPullback P₀.A P₁.A (spMap τ) j ∧ IsGrpPullback P₁.A G v k₀ ∧
      e ≫ j = 𝟙 _ ∧ LBIso (ρ.P.L.pull b) (N.pull (j ≫ k₀ ≫ β)) ∧
      ∀ x (w : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
        ∃ w₀ : Sp Ω ⟶ P₁.A.left, w₀ ≫ P₁.A.hom = 𝟙 _ ∧ w₀ ≫ e = spMap σ ≫ w ∧
          w₀ ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt (l' (a x))).left := by
  obtain ⟨P₁, a₁, a₁', ha₁, ha₁', la₁, la₁', hp₁⟩ := h'
  rw [RingHom.id_comp] at ha₁ hp₁
  have := mono_val S.R S.frac
  have : Mono b := (MorphismProperty.monomorphisms Scheme).of_isPullback hb.1.flip (.infer_property _)
  obtain ⟨κ, hκ, lκ, eκ⟩ := exists_factor ρ.P P₀ P₁ (Category.id_comp _) hb ha₁ lb la₁
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  have e₁ : spMap τ ≫ spMap σ = 𝟙 (Sp Ω) := (sp_comp hτ).trans hid
  have e₂ : spMap σ ≫ spMap τ = 𝟙 (Sp Ω) := (sp_comp hσ).trans hid
  have he : IsGrpPullback P₁.A P₀.A (spMap σ) (κ ≫ t) := (hκ.comp ht).congr (Category.id_comp _) rfl
  have le := lb_comp P₁.isLB P₀.isLB P₀.isLB lκ lt
  have : IsIso (spMap σ) := ⟨_, e₂, e₁⟩
  have : Mono (κ ≫ t) := (MorphismProperty.monomorphisms Scheme).of_isPullback he.1.flip (.infer_property _)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 P₀.A))
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P₀ P₁ P₀ (ψ := 𝟙 _) e₁ he (isGrpPullback_of_iso (Iso.refl P₀.A)) le
    ((iso_iff P₀.isLB P₀.isLB _).2 (by rw [GlobalTheory.CechPic.pull_id]; try rfl))
  have w₁ : a₁' ≫ ρ'.P.A.hom = (P₁.A.hom ≫ v) ≫ r := by rw [ha₁'.1.w, Category.assoc, hv]
  have k₁ := hα.1.lift_fst _ _ w₁
  have k₂ := hα.1.lift_snd _ _ w₁
  generalize hα.1.lift _ _ w₁ = k₀ at k₁ k₂
  have hs : ∀ x, (ρ.pt x).left ≫ ρ.P.A.hom = 𝟙 _ := fun x => Over.w (ρ.pt x)
  refine ⟨P₁, κ ≫ t, j, k₀, he, hj, hα.cancel (ha₁'.congr hv.symm k₁.symm) k₂, ?_, ?_, fun x w hw => ?_⟩
  · rw [← cancel_mono (κ ≫ t), Category.assoc, ej, Category.comp_id, Category.id_comp]
  · have c₁ := (iso_iff (pull_isLB ρ'.P.isLB α) hN β).1 hL
    rw [cls_pull ρ'.P.isLB] at c₁
    rw [iso_iff (pull_isLB ρ.P.isLB b) hN, cls_pull ρ.P.isLB, ← (iso_iff P₀.isLB ρ.P.isLB _).1 lb,
      (iso_iff P₀.isLB P₁.isLB _).1 lj, (iso_iff P₁.isLB ρ'.P.isLB _).1 la₁', ← k₁, pull_comp, pull_comp, pull_comp, c₁]
  · obtain ⟨u, f₁, f₁'⟩ := hp₁ (a x)
    have k₃ : w ≫ P₀.A.hom = 𝟙 _ := by
      rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← hb.1.w, reassoc_of% hw, hs]
      simp
    have c₂ : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, k₃]; simp
    have k₄ := ht.1.lift_fst _ _ c₂
    generalize ht.1.lift _ _ c₂ = w' at k₄
    have k₅ : u ≫ κ = w' := by
      rw [← cancel_mono b, Category.assoc, eκ, f₁, hp x w w' hw k₄]
    refine ⟨u, ?_, by rw [reassoc_of% k₅, k₄], by rw [k₁, f₁']⟩
    rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← ha₁.1.w, reassoc_of% f₁, hs]
    simp

theorem exists_conj_uWit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hs hu G _ α β hα hβ hL
  obtain ⟨P₀, b, t, hb, ht, lb, lt, hp⟩ := hG
  obtain ⟨P₁, e, j, k₀, he, hj, hk, ej, hL', hpt⟩ := exists_twist_along_genericAutomorphism D.X.ρ ρ' _ hs (σ : D.X.Ω₁ →+* D.X.Ω₁)
    (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) (RingHom.ext fun x => σ.symm_apply_apply x) (RingHom.ext fun x => σ.apply_symm_apply x)
    a P₀ b t hb ht lb lt hp (spMap_val_toRat R') G α hα _ Xo.univ.t.PP.isLB β hL
  have h₁ : spMap (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.uΩ = D.X.uΩ := by
    rw [D.pt, ← Category.assoc, sp_comp (RingHom.ext fun x => σ.symm.commutes x)]
  have hβ' : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (j ≫ k₀ ≫ β) :=
    (hj.comp (hk.comp hβ)).congr (by rw [← Category.assoc _ u', hu, ← Category.assoc, h₁]) rfl
  exact ⟨{ G := P₀.A, α := b, β := j ≫ k₀ ≫ β, hα := hb, hβ := hβ', hL := hL' }, P₁.A, inferInstance, e, k₀, he, hk,
    by rw [reassoc_of% ej], hpt⟩

end GlobalTheory.UPoinc.UGalTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  first | exact @GlobalTheory.MumProd.exists_cubeIso | exact GlobalTheory.MumProd.exists_cubeIso | (intros; apply GlobalTheory.MumProd.exists_cubeIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeProductTwistedSectionsVanishing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem prod_tφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X)
    {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (tφ D a β k) ^ tε n j k =
      h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * h ((toUnit D.P.A ≫ D.c β) * 𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (h (toUnit D.P.A ≫ D.c β).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left * h a.left ^ j := by
  rw [Fin.prod_univ_five, _root_.mul_comm (toUnit D.P.A ≫ D.c β)]
  simp only [← zpow_neg_one]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _)) rfl)
    (zpow_one _)) rfl

theorem exists_isProdT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j n' j' : ℤ)
    (β β' : D.X) (f : SecT D a n j β) (g : SecT D a n' j' β') :
    ∃ p : SecT D a (n + n') (j + j') (β + β'), IsProdT f g p := by
  have hadd : toUnit D.P.A ≫ D.c (β + β') = (toUnit D.P.A ≫ D.c β) * (toUnit D.P.A ≫ D.c β') := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have hu := DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen
    (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := tφ D a (β + β')) (ε' := tε (n + n') (j + j')) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_tφ_eq D a n j β h) (prod_tφ_eq D a n' j' β' h)))
        (prod_cub (toUnit D.P.A ≫ D.c β) (toUnit D.P.A ≫ D.c β') (𝟙 D.P.A) h))).trans ?_
      rw [prod_tφ_eq, hadd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec _ hu))
  refine ⟨p, fun Z x z J hJ => (hp Z x z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val (val_pull hJ _ _ _)))))⟩

theorem exists_prodT_van : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  intro R _ _ _ _ D a n j n' j' n'' j'' hn hj β β' f g
  subst hn hj
  obtain ⟨p, hp⟩ := exists_isProdT D.toPre a n j n' j' β β' f g
  refine ⟨p, hp, fun e he Z x z J hJ => ?_⟩
  rw [hp Z _ z J hJ]
  rcases he with he | he
  · rw [he Z x z J hJ, zero_mul, zero_mul]
  · rw [he Z x z J hJ, mul_zero, zero_mul]

end GlobalTheory.TwFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureSemiAbelianExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem exists_cp_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric Z.L Z.sym

  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hO.ne (Set.mem_univ w)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _

  have w' : pullback.fst Z.G.hom M.pt ≫ Z.G.hom = (((Over.pullback M.pt).obj Z.G).hom ≫ x) ≫ U₀.ι := by
    rw [Category.assoc, hx]; exact pullback.condition
  let φ' := Z.cart.1.lift (pullback.fst Z.G.hom M.pt) (((Over.pullback M.pt).obj Z.G).hom ≫ x) w'
  have n : IsGrpPullback ((Over.pullback M.pt).obj Z.G) Z.G (x ≫ U₀.ι) (φ' ≫ Z.φ) :=
    (isGrpPullback_pullback Z.G M.pt).congr hx.symm (Z.cart.1.lift_fst _ _ _).symm
  have h1 := IsGrpPullback.cancel Z.cart n (Z.cart.1.lift_snd _ _ _)
  have h2 := (IsGrpPullback.comp h1 (isGrpPullback_pullback ρS.P.A Z.u₀)).congr (Z.u₀_gen x hx) rfl
  have hA : IsAbelianScheme ((Over.pullback M.pt).obj Z.G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback ρS.P.isAb h2
  have h3 := GlobalTheory.ValueForm.surjective_cube_baseChange GlobalTheory.globalFns_holds M.pt hA (Iso.refl _)

  have := Z.semi.smooth
  have : Flat (G3 Z.G).hom := by
    show Flat (pullback.fst Z.G.hom (pullback.fst Z.G.hom Z.G.hom ≫ Z.G.hom) ≫ Z.G.hom)
    infer_instance
  have := M.sep
  have : QuasiCompact M.pt := by infer_instance
  have : IsSchemeTheoreticallyDominant M.pt := IsSchemeTheoreticallyDominant.of_isDominant M.pt
  have : IsSchemeTheoreticallyDominant (pullback.fst (G3 Z.G).hom M.pt) :=
    .of_isPullback (IsPullback.of_hasPullback (G3 Z.G).hom M.pt).flip
  have hi : ∀ U, Function.Injective ((pullback.fst (G3 Z.G).hom M.pt).app U).hom :=
    fun U => (pullback.fst (G3 Z.G).hom M.pt).app_injective U
  exact ⟨⟨Z.L, Z.cub, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange M.pt hi h3 Z.cub s hs hr⟩, rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamRingAction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum.DRAct

section Pull

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} (κ : DividedPowers I) (t : S ⟶ Sp R)
  {A : Over S} [GrpObj A]

theorem primPull_of_eq_id (f : A ⟶ A) [IsMonHom f] (h : f = 𝟙 A) (c : prim κ t A) : primPull κ t f c = c := by
  subst h
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem primPull_of_eq_comp (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f ≫ g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f (primPull κ t g c) := by
  subst h
  exact (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c).symm

theorem primPull_of_eq_mul (f g k : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom k] (h : k = f * g)
    (c : prim κ t A) : primPull κ t k c = primPull κ t f c + primPull κ t g c := by
  subst h
  exact Subtype.ext (c.2 A f g)

end Pull

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] (i : OAct O A)

theorem actPull_one {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) : actPull i 1 hV c = c :=
  haveI := i.hom
  primPull_of_eq_id _ _ _ (by rw [i.one, CategoryTheory.Functor.map_id]) c

theorem actPull_mul (x y : O) {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) :
    actPull i (x * y) hV c = actPull i x hV (actPull i y hV c) :=
  haveI := i.hom
  primPull_of_eq_comp _ _ _ _ _ (by rw [i.mul, CategoryTheory.Functor.map_comp]) c

theorem actPull_add (x y : O) {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) :
    actPull i (x + y) hV c = actPull i x hV c + actPull i y hV c :=
  haveI := i.hom
  primPull_of_eq_mul _ _ _ _ _ (by rw [i.add]; exact CategoryTheory.Functor.map_mul _ _ _) c

theorem transition_comm (f : A ⟶ A) {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    {b : Sp Γ(T, V') ⟶ Sp Γ(T, V)} {φ : (onAff A hV').left ⟶ (onAff A hV).left}
    (w : φ ≫ (onAff A hV).hom = (onAff A hV').hom ≫ b)
    (hφ : φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec) :
    φ ≫ ((Over.pullback hV.fromSpec).map f).left = ((Over.pullback hV'.fromSpec).map f).left ≫ φ := by
  have k {W : T.Opens} (hW : IsAffineOpen W) :
      ((Over.pullback hW.fromSpec).map f).left ≫ pullback.fst A.hom hW.fromSpec =
        pullback.fst A.hom hW.fromSpec ≫ f.left := pullback.lift_fst _ _ _
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) (k hV)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f.left) hφ).trans ?_)
    refine (k hV').symm.trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg (_ ≫ ·) hφ.symm
  · refine (Category.assoc _ _ _).trans
      ((congrArg (φ ≫ ·) (Over.w ((Over.pullback hV.fromSpec).map f))).trans (w.trans ?_))
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) w.symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ b) (Over.w ((Over.pullback hV'.fromSpec).map f)).symm

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

theorem actPull_res (he : IsDRIso A H e) (x : O) {V V' : T.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(H, V)) :
    (e V' hV').symm (actPull i x hV' (e V' hV' (Twist.resM H h s))) =
      Twist.resM H h ((e V hV).symm (actPull i x hV (e V hV s))) := by
  letI := resAlg h
  haveI := i.hom x
  obtain ⟨φ, hφ, hφ'⟩ := DeRhamSheaf.VB.exists_transition A hV hV' h
  have a := he V V' hV hV' h φ hφ hφ'
  refine (e V' hV').symm_apply_eq.2 (Eq.trans ?_ (a _).symm)
  refine (congrArg (actPull i x hV') (a s)).trans ?_
  refine Eq.trans ?_
    (congrArg (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull ((e V hV).apply_symm_apply _).symm)
  have m := homMor (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV)
    ((Over.pullback hV.fromSpec).map (i.act x))
  have m' := homMor (dp0 Γ(T, V')) (𝟙 _) (A := onAff A hV') (B := onAff A hV')
    ((Over.pullback hV'.fromSpec).map (i.act x))
  have k := m.comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  exact (GrpMor.pull_pull (GlobalTheory.Published.AbelianDeRham.bcMor hφ) m' k (fun _ ↦ rfl)
    (transition_comm (i.act x) hV hV' hφ.1.w hφ').symm _).trans
    (GrpMor.pull_pull m (GlobalTheory.Published.AbelianDeRham.bcMor hφ) k (fun _ ↦ rfl) rfl _).symm

theorem exists_hom (he : IsDRIso A H e) (x : O) :
    ∃ u : H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV (u.app V s) = actPull i x hV (e V hV s) := by
  obtain ⟨u, hu⟩ := GlobalTheory.hom_of_affine_compatible T H H
    (fun V hV ↦ (e V hV).symm.toLinearMap ∘ₗ actPull i x hV ∘ₗ (e V hV).toLinearMap)
    fun V V' hV hV' h s ↦ actPull_res i e he x hV hV' h s
  exact ⟨u, fun V hV s ↦ (congrArg (e V hV) (LinearMap.congr_fun (hu V hV) s)).trans
    ((e V hV).apply_symm_apply _)⟩

end GlobalTheory.AbDatum.DRAct

open GlobalTheory.AbDatum.DRAct in

theorem GlobalTheory.AbDatum.exists_isDRAct : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A],
    IsAbelianScheme A → ∀ (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ ρ : O →+* End H, IsDRAct e i ρ := by
  intro O _ T A _ _ i H e he
  choose u hu using exists_hom i e he
  have h1 : u 1 = 𝟙 H := hom_ext_affine fun V hV s ↦
    (e V hV).injective ((hu 1 V hV s).trans (actPull_one i hV (e V hV s)))
  have h2 (x y : O) : u (x * y) = u y ≫ u x := hom_ext_affine fun V hV s ↦ by
    change (u (x * y)).app V s = (u x).app V ((u y).app V s)
    apply (e V hV).injective
    rw [hu, hu, hu, actPull_mul]
  have h3 (x y : O) : u (x + y) = u x + u y := hom_ext_affine fun V hV s ↦ by
    change (u (x + y)).app V s = (u x).app V s + (u y).app V s
    apply (e V hV).injective
    rw [map_add, hu, hu, hu, actPull_add]
  exact ⟨RingHom.mk' { toFun x := (u x : End H), map_one' := h1, map_mul' := h2 } h3, hu⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribMulAction.toAddMonoidHom D'.toPre.X F.e) y) (((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumFam.FactorAdj.exists_pull | exact GlobalTheory.MumFam.FactorAdj.exists_pull | (intros; apply GlobalTheory.MumFam.FactorAdj.exists_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedLineBundleEquivariantGeneratorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_lineBundle_equivariantGenerator : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∃ (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), M.IsLB ∧ IsEquivGen i q χ M e := by
  first | exact @GlobalTheory.CharKer.exists_equivGen | exact GlobalTheory.CharKer.exists_equivGen | (intros; apply GlobalTheory.CharKer.exists_equivGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

open GlobalTheory.SmoothLift

attribute [local instance] opK isCentral_K isTower_K

set_option maxHeartbeats 4000000 in

theorem exists_retraction : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T)
    (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T)
    (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T),
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧
      (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧
      (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧
    (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧
      (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  intro R _ I κ X t
  have hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ := fun T ↦ (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R T.B T.J T.δ).1
  have H := fun T : Thick κ t ↦ GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R T.B T.J T.δ (ER T) (nb T).J (nb T).δ (fstA T) (sndA T)
    (sndA_mul T) (sndA_algebraMap T) (fun n a ha ↦ sndA_dpow T n a ha)
  choose ρ ha hm h0 h1 hrel hone hdeg using H
  have natK : ∀ (j : ℕ) (T T' : Thick κ t) (φ : T ⟶ T') (x : K R (nb T).δ j),
      rK (nb T').δ (ha T') (hrel T') (hdeg T') j (km (SemiHom.of_algHom (nbAlg φ)) (nbF.map φ).dp j x) =
        km (SemiHom.of_algHom φ.φ) φ.dp j (rK (nb T).δ (ha T) (hrel T) (hdeg T) j x) := by
    intro j T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : (x : DR R (ER T)) ∈ ⋀[ER T]^j Ω[ER T⁄R] := x.2
    have hd := hdeg T j _ hx
    let y := hd.choose
    have hy : y ∈ ⋀[T.B]^j Ω[T.B⁄R] := hd.choose_spec.1
    have hρy : ρ T x - y ∈ rel R T.δ := hd.choose_spec.2
    rw [rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (y := ⟨y, hy⟩) hρy, km_mk]
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') x)
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hρy)
    rw [map_sub, sub_add_sub_cancel] at e
    exact rK_spec (nb T').δ (ha T') (hrel T') (hdeg T') (x := (SemiHom.of_algHom (nbAlg φ)).mOm j x)
      (y := (SemiHom.of_algHom φ.φ).mOm j ⟨y, hy⟩) e
  have uK : ∀ (j : ℕ), j ≠ 0 → ∀ (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (inlMap T).φ) (inlMap T).dp j x) = 0 := by
    intro j hj T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x
    rw [algebraMapInv_eq_zero hj x.2, map_zero] at e
    have e' : ρ T ((SemiHom.of_algHom (inlMap T).φ).mDR x) - ((0 : Om R T.B j) : DR R T.B) ∈ rel R T.δ := by
      rw [ZeroMemClass.coe_zero]; exact e
    exact (rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (inlMap T).φ).mOm j x) e').trans
      (Submodule.Quotient.mk_zero _)
  have vK : ∀ (j : ℕ) (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (difMap T).φ) (difMap T).dp j x) = x := by
    intro j T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (difMap T).φ).mOm j x) (y := x)
      (vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x)
  refine ⟨nbF, uN, vN, fun T ↦ r1 (nb T).δ (ha T) (hrel T) (hone T), fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 2,
    fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 3, ⟨?_, ?_, ?_⟩, ⟨fun T T' φ x ↦ natK 2 T T' φ x,
      fun T x ↦ uK 2 (by norm_num) T x, fun T x ↦ vK 2 T x⟩, fun T T' φ x ↦ natK 3 T T' φ x,
      fun T x ↦ uK 3 (by norm_num) T x, fun T x ↦ vK 3 T x⟩
  · intro T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd := hone T x
    let ω := hd.choose
    have hω : ρ T (ι1 x) - ι1 ω ∈ rel R T.δ := hd.choose_spec
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') (ι1 x))
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hω)
    rw [map_sub, sub_add_sub_cancel, SemiHom.mDR_ι, SemiHom.mDR_ι] at e
    have l := divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := x) hω
    exact (divPowerCompatOneForm_retraction_spec (nb T').δ (ha T') (hrel T') (hone T') (x := (SemiHom.of_algHom (nbAlg φ)).m1 x)
      (ω := (SemiHom.of_algHom φ.φ).m1 ω) e).trans (congrArg (km1 (SemiHom.of_algHom φ.φ) φ.dp) l).symm
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    have z : ExteriorAlgebra.algebraMapInv (ι1 x) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    rw [z, map_zero, SemiHom.mDR_ι] at e
    have e' : ρ T (ι1 ((SemiHom.of_algHom (inlMap T).φ).m1 x)) - ι1 (0 : Ω[T.B⁄R]) ∈ rel R T.δ := by
      rw [map_zero]; exact e
    exact (divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (inlMap T).φ).m1 x) e').trans
      (Submodule.Quotient.mk_zero _)
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    rw [SemiHom.mDR_ι] at e
    exact divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (difMap T).φ).m1 x) (ω := x) e

end GlobalTheory.PDForm.Nbhd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalStabiliserMulMemBigCellInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonalStabiliser_mul_mem_bigCell_inert : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.DblVac.exists_diag_mul_bigCell | exact GlobalTheory.DblVac.exists_diag_mul_bigCell | (intros; apply GlobalTheory.DblVac.exists_diag_mul_bigCell <;> assumption)
end

