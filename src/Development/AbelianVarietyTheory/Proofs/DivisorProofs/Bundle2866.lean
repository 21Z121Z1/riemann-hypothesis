import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0948
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalUniq

open TopologicalSpace

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}

theorem w_trans (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen) {Z : Scheme.{0}} (χ : Z ⟶ X') (z : Z)
    {jj jj' : K₀ → M.ι} {k k' : M'.ι} (h₁ : χ z ∈ LB.wchart M ψ jj) (h₁' : χ z ∈ LB.wchart M ψ jj')
    (h₂ : χ z ∈ M'.U k) (h₂' : χ z ∈ M'.U k') :
    gm χ z (LB.wchart M ψ jj ⊓ M'.U k) (w.s (jj, k)) =
      (∏ i, gm (χ ≫ ψ i) z (M.U (jj i) ⊓ M.U (jj' i)) (M.g (jj i) (jj' i)) ^ δ i) *
        (gm χ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * gm χ z (LB.wchart M ψ jj' ⊓ M'.U k') (w.s (jj', k')) := by
  have hm : χ z ∈ LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm χ z (LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k'))) (hw (jj, k) (jj', k'))
  have d := gm_div M' (LB.LinComb M ψ δ) χ z (jj, k) (jj', k') hm
  have l := gm_linComb M ψ δ χ z jj jj' h₁ h₁'
  exact (gm_res χ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res χ z _ hm _))))

theorem prod_split {G : Type} [CommGroup G] {K : Type} [Fintype K] (ε : K → ℤ) (f : K × K₀ → G) :
    ∏ p, f p ^ (ε p.1 * δ p.2) = ∏ a, (∏ i, f (a, i) ^ δ i) ^ ε a := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

section Gen

variable {K : Type} [Fintype K] {φ' : K → (Y ⟶ X')} {ε : K → ℤ}

theorem chart_le (j : K × K₀ → M.ι) (q : K → M'.ι) (a : K) :
    LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (a, k), Set.mem_iInter.1 hy.2 a⟩

def locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)ˣ :=
  (∏ a, res (chart_le j q a) (pullU (φ' a) _ (w.s (fun k => j (a, k), q a))) ^ ε a) * res inf_le_right (t'.s q)

theorem gm_locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) :
    gm r z (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) (locU w t' j q) =
      (∏ a, gm (r ≫ φ' a) z (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a))
        (w.s (fun k => j (a, k), q a)) ^ ε a) * gm r z (LB.wchart M' φ' q) (t'.s q) := by
  refine (map_mul (gm r z _) _ _).trans (congrArg₂ (· * ·) ((map_prod (gm r z _) _ _).trans
    (Finset.prod_congr rfl fun a _ => ?_)) ?_)
  · refine (map_zpow (gm r z _) _ _).trans (congrArg (· ^ ε a) ?_)
    have hm : r z ∈ φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := chart_le (δ := δ) j q a hz
    have h1 := gm_res r z (chart_le (δ := δ) j q a) hz (pullU (φ' a) _ (w.s (fun k => j (a, k), q a)))
    have h2 := gm_pull r (φ' a) z ((LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a)) hm
      (w.s (fun k => j (a, k), q a))
    exact h1.trans h2
  · exact gm_res r z (inf_le_right : LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      LB.wchart M' φ' q) hz (t'.s q)

theorem exists_gen_iso (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J →
        Good M' z J' → val u r z J = (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' := by
  have tr : ∀ (j : K × K₀ → M.ι) (q q' : K → M'.ι) (y : Y),
      y ∈ (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) ⊓
        (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q') →
      gm (𝟙 Y) y _ (locU w t' j q) = gm (𝟙 Y) y _ (locU w t' j q') := by
    intro j q q' y hy
    rw [gm_locU w t' j q (𝟙 Y) y hy.1, gm_locU w t' j q' (𝟙 Y) y hy.2, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
    simp only [trF, Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a)) (w.s (fun k => j (a, k), q a)) =
        (gm (φ' a) y (M'.U (q a) ⊓ M'.U (q' a)) (M'.g (q a) (q' a)))⁻¹ *
          gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q' a)) (w.s (fun k => j (a, k), q' a)) := by
      intro a
      have m := chart_le (δ := δ) j q a hy.1
      have m' := chart_le (δ := δ) j q' a hy.2
      rw [w_trans w hw (φ' a) y m.1 m.1 m.2 m'.2, Finset.prod_eq_one fun i _ => ?_, _root_.one_mul]
      exact (congrArg (· ^ δ i) (gm_self hM _ y (Set.mem_iInter.1 hy.1.1 (a, i)))).trans (one_zpow _)
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a)]
    simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : K × K₀ → M.ι, ∃ s : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j)ˣ,
      ∀ q, res inf_le_left s = locU w t' j q := fun j =>
    glue_unit _ (fun q => LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)
      (fun _ => inf_le_left) (fun y hy => by
        choose b hb using fun a => exists_chart hM' (φ' a y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy, Set.mem_iInter.2 hb⟩) (locU w t' j) (tr j)
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K × K₀ → M.ι) (q : K → M'.ι)
      (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q),
      gm r z _ (s j) = gm r z _ (locU w t' j q) := fun Z r z j q hz =>
    (gm_res r z inf_le_left hz (s j)).symm.trans (congrArg (gm r z _) (hs j q))
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose b hb using fun a => exists_chart hM' (φ' a y)
    have hq : y ∈ LB.wchart M' φ' b := Set.mem_iInter.2 hb
    erw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_linComb M _ (fun p : K × K₀ => ε p.1 * δ p.2) (𝟙 Y) y j j' hy.1 hy.2]
    erw [hv Y (𝟙 Y) y j b ⟨hy.1, hq⟩, hv Y (𝟙 Y) y j' b ⟨hy.2, hq⟩, gm_locU w t' j b (𝟙 Y) y ⟨hy.1, hq⟩,
      gm_locU w t' j' b (𝟙 Y) y ⟨hy.2, hq⟩]
    simp only [Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j (a, k), b a)) =
        (∏ i, gm (φ' a ≫ ψ i) y (M.U (j (a, i)) ⊓ M.U (j' (a, i))) (M.g (j (a, i)) (j' (a, i))) ^ δ i) *
          gm (φ' a) y (LB.wchart M ψ (fun k => j' (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j' (a, k), b a)) := by
      intro a
      have m := chart_le (δ := δ) j b a ⟨hy.1, hq⟩
      have m' := chart_le (δ := δ) j' b a ⟨hy.2, hq⟩
      rw [w_trans w hw (φ' a) y m.1 m'.1 m.2 m.2, gm_self hM' _ y m.2, inv_one, _root_.mul_one]
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a), prod_split ε]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [_root_.mul_assoc]
  · have hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => J (r ≫ φ' p.1 ≫ ψ p.2)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := ⟨hJ.mem _ r, hJ'.mem φ' r⟩
    refine (hv Z r z _ _ hz).trans ((gm_locU w t' _ _ r z hz).trans ?_)
    refine congrArg (· * _) (Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) ?_)
    unfold GlobalTheory.TensBal.isoV
    have : (fun k => J ((r ≫ φ' a) ≫ ψ k)) = fun k => J (r ≫ φ' a ≫ ψ k) := funext fun k => by rw [Category.assoc]
    rw [this]
    rfl

end Gen

theorem iso_unique : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  intro X X' Y S₀ M M' hM hM' K₀ _ ψ δ w hw K K₁ _ _ φ' ε φ ε₁ hF t' ht' t ht p e he hp h Z r z J J' hJ hJ'
  obtain ⟨u, hu, hv⟩ := exists_gen_iso hM hM' w hw ht'
  have key := gen_unique' hM hF p e he hp ht hu (fun y I hI => by
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    exact (h y I I' hI hI').symm.trans (hv _ e y I I' hI hI').symm) Z r z J hJ
  exact (hv Z r z J J' hJ hJ').symm.trans key.symm

end GlobalTheory.TensBalUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map_eq {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem exists_fixed_of_mem_span {D : D7} (j : Fin D.R.m) {W M : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (Φ : W →ₗ[ℂ] M) (c : VsV D j ℂ →ₗ[ℂ] W) (a₀ : ℂ) (S : Set (VV (↥D.LL0) (lamV D j))) {P : M}
    (hP : P ∈ Submodule.span (smallInt D)
      {P | ∃ Fv ∈ S, P = Φ (c (a₀ • GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv))}) :
    ∃ y : VsV D j ℂ, P = a₀ • Φ (c y) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjVec j τ y y := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Fv, -, rfl⟩ := hP
    refine ⟨GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv, by rw [c.map_smul, Φ.map_smul], fun τ hτ => ?_⟩
    change MvPolynomial.map _ _ = MvPolynomial.map _ (MvPolynomial.map _ _)
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp (Formalism.L2.Host.embLL0 D) = Formalism.L2.Host.embLL0 D from RingHom.ext hτ]
  | zero => exact ⟨0, by rw [c.map_zero, Φ.map_zero, smul_zero], fun τ _ => (map_zero _).symm⟩
  | add P₁ P₂ _ _ h1 h2 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    obtain ⟨y2, rfl, c2⟩ := h2
    refine ⟨y1 + y2, by rw [c.map_add, Φ.map_add, smul_add], fun τ hτ => ?_⟩
    have e1 := c1 τ hτ
    have e2 := c2 τ hτ
    unfold ConjVec at e1 e2 ⊢
    rw [Submodule.coe_add, map_add, ← e1, ← e2]
  | smul a P₁ _ h1 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    refine ⟨(a : ℂ) • y1, ?_, fun τ hτ => ?_⟩
    · rw [c.map_smul, Φ.map_smul, smul_comm a₀]
      rfl
    · have e1 := c1 τ hτ
      unfold ConjVec at e1 ⊢
      obtain ⟨o, ho⟩ := a.2
      have ha : (τ : ℂ →+* ℂ) (a : ℂ) = a := by rw [← ho]; exact hτ _
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← e1, ha]

set_option maxHeartbeats 4000000 in

theorem coefAt_of_twAdm : TwAdm → CoefAt := by
  intro hA
  refine AtTw.imp (AtTw.and hA lowAt_holds) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨-, -, hin⟩, hlow⟩ := H
  have hR := ratHyp0_at_point Fm x hx i p hr hm _ hin hlow j
  intro ρ ν hρ hp hN
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := hN
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨c, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => p.P.A3.A.μ0) (p.O j)
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo := baseOf_of_realPin hR.core.lev hρ hp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have H1 := GlobalTheory.CoefLatConj.coefLat_conj (Fm.D x i) _ _ _ p.P.A3.A p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O hR.core hR.fw hR.io j
    hR.pins c hc u hu _ hB hBo
  obtain ⟨κ, hκ0, hκ, H2⟩ := H1
  have hspan := (H2.2 _ (Formalism.L2.Host.embLL0 _) (labLL0 _) (smallInt _) (smallInt_isCoefRing _)).1

  have hO : OMPins p.T p.R.toRealDat p.κ p.v₀ p.O j := hR.pins
  have hfield := hO.2.lift.field
  have hc0 := hO.2.lift.c0
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hc0
  have hcL : ∀ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j),
      c (GlobalTheory.CoefModel.mapVV (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map (Fm.D x i).what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (p.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map_eq _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq_of_isScale p.R p.v₀ _ hsc hκs
  have hφc : phs p j * c₀ ≠ 0 := fun h0 => hν0 ((pow_eq_zero_iff hn).1 (hνn.trans (by rw [h0, zero_pow hn])))
  have hφ : phs p j ≠ 0 := left_ne_zero_of_mul hφc
  refine ⟨c, u, ν / (phs p j * κ), hc, hu, ⟨n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩, ?_⟩
  · have e : ν ^ (n * k) = (phs p j * κ) ^ (n * k) := by
      rw [pow_mul, hνn, ← pow_mul, mul_pow, mul_pow, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
    rw [div_pow, e, div_self (pow_ne_zero _ (mul_ne_zero hφ hκ0))]
  · intro h₀ P hP
    obtain ⟨y, hPy, hy⟩ := exists_fixed_of_mem_span j (p.R.ioP j (PiTensorProduct.tprod ℂ u)) c κ⁻¹ _
      ((hspan (finPt _ h₀)).le hP)
    refine ⟨y, ?_, hy⟩
    have e : ν * κ⁻¹ = ν / (phs p j * κ) * phs p j := by field_simp
    exact (congrArg (ν • ·) hPy).trans ((smul_smul ν κ⁻¹ _).trans (congrArg (· • _) e))

end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RigLinUnique

theorem eq_pull_section {X S S' : Scheme.{0}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (j : S' ⟶ S)
    (hi : Function.Injective (pullback.fst p j).appTop.hom)
    (hs : Function.Surjective (pullback.snd p j).appTop.hom) (u : Γ(X, ⊤)) :
    u = p.appTop.hom (e.appTop.hom u) := by
  have cmp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Γ(C, ⊤)),
      a.appTop.hom (b.appTop.hom x) = (a ≫ b).appTop.hom x := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  obtain ⟨c, hc⟩ := hs ((pullback.fst p j).appTop.hom u)
  let e' : S' ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 S') (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have h2 : e' ≫ pullback.snd p j = 𝟙 S' := pullback.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom u) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h1, h2, ← cmp, Scheme.Hom.id_appTop] at this
    exact this
  apply hi
  rw [cmp, pullback.condition, ← cmp, ← hc', hc]

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (g y) ∈ L.U j → g y ∈ L'.U k →
      gw w₂ g y j k = gm g y ⊤ u * gw w₁ g y j k := by
  have key : ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι),
      gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w₂.s (fun _ => j, k) * (w₁.s (fun _ => j, k))⁻¹) =
        gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := fun Y g y j k =>
    (map_mul _ _ _).trans (congrArg (gw w₂ g y j k * ·) (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit (X := X') (J := L.ι × L'.ι) ⊤ (fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2)
    (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩)
    (fun p => w₂.s (fun _ => p.1, p.2) * (w₁.s (fun _ => p.1, p.2))⁻¹) (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      refine (key _ _ x p.1 p.2).trans (Eq.trans ?_ (key _ _ x q.1 q.2).symm)
      rw [a, b, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨u, fun Y g y j k hj hk => ?_⟩
  have hm : g y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have : gm g y ⊤ u = gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := (gm_res g y le_top hm u).symm.trans
    ((congrArg (gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k)) (hu (j, k))).trans (key Y g y j k))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

theorem gw_eq_of_rigidified : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  intro R' _ _ _ D' A' G' _ _ hS U' s f₁ f₂ hf he₁ he₂ w₁ w₂ g₁ g₂ m₁ m₂ z j k hk hj
  subst hf
  have hL := U'.LG.isLB
  obtain ⟨u, hu⟩ := exists_ratio hL hL w₁ w₂ ((isGen_iff w₁).1 g₁) ((isGen_iff w₂).1 g₂)
  have p₁ := (maps_iff w₁ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₁ U'.LG.L)
    (fun _ => rfl)).1 m₁
  have p₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₂ U'.LG.L)
    (fun _ => rfl)).1 m₂
  have he1 : pullU (eSec G') ⊤ u = 1 := by
    apply unit_ext
    intro x _
    obtain ⟨a, ha⟩ := exists_chart hL (f₁ (eSec G' x))
    obtain ⟨b, hb⟩ := exists_chart hL (eSec G' x)
    have q₁ := p₁ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q₂ := p₂ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q := mul_right_cancel (q₂.symm.trans q₁)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hu _ (𝟙 _ ≫ eSec G') x a b ha hb] at q
    rw [map_one]
    exact (gm_pull (𝟙 _) (eSec G') x ⊤ trivial u).trans (mul_eq_right.1 q)
  have := U'.smooth
  have : Flat G'.hom := inferInstance
  have : IsDominant (jK R') := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap R' (FractionRing R')))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R' (FractionRing R'))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R')
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R')) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G'.hom (jK R')).flip
  have hb := GlobalFunctionsDvrPowers.bijective_of_iso U'.gen (GlobalTheory.SemiRigid.globalFns _ A'.A A'.isAb)
  have hv := eq_pull_section G'.hom (eSec G') (Over.w η[G']) (jK R')
    ((pullback.fst G'.hom (jK R')).app_injective ⊤) hb.2 u.val
  have he2 : (eSec G').appTop.hom u.val = 1 := congrArg Units.val he1
  have hu1 : u = 1 := Units.ext (hv.trans ((congrArg G'.hom.appTop.hom he2).trans (map_one _)))
  rw [hu _ (𝟙 _) z j k hj hk, hu1, map_one, _root_.one_mul]

end GlobalTheory.Mum.RigLinUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem eq_torusMap_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X →+ X)
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem endChar_endU : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  intro V₁ _ _ _ _ D P G _ _ _ U E κ _ a ha G₀ _ φ h f₀ hf
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V₁ (maximalIdeal V₁) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

open GlobalTheory.TorsionFormCompare GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum in

theorem hasUnif_of_iso {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (G G₀ : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀]
    [IsCommMonObj G₀] (ε : G ≅ G₀) (hε : IsMonHom ε.hom) (hsa : IsSemiAbelian G₀) (L₀ : LB G₀.left)
    (h : HasUnif G₀ L₀) : HasUnif G (L₀.pull ε.hom.left) := by
  obtain ⟨D, A₀, U₀, hL⟩ := h
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists V (IsLocalRing.maximalIdeal V) hR D
  obtain ⟨hD, -⟩ := exists_isIdPull V D.toPre W hW hψ
  obtain ⟨bc, U, -, -, hLG, -, -⟩ :=
    exists_unif_move V (IsLocalRing.maximalIdeal V) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  refine ⟨D, A₀, U, ?_⟩
  rw [hLG]
  exact LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hL

theorem unifAlong_bG {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (f : Sp R ⟶ S) (hG : IsSemiAbelian G) (h : UnifAlong G L.L) : UnifAlong (bG G f) (bL L f).L := by
  intro V _ _ _ _ hV hf ξ hξ _
  have hξ' : ((ξ ≫ f) ⁻¹' abLocus G).Nonempty := by
    obtain ⟨p, hp⟩ := hξ
    refine ⟨p, ?_⟩
    have := (abLocus_pullback (G' := bG G f) abLocusOne hG (isGrpPullback_pullback G f).1 (ξ p)).2 hp
    simpa using this
  obtain ⟨ε, hε, hφ⟩ := grpPullback_iso ((isGrpPullback_pullback (bG G f) ξ).comp (isGrpPullback_pullback G f))
    (isGrpPullback_pullback G (ξ ≫ f))
  obtain ⟨D, A, U, hU⟩ := hasUnif_of_iso hV _ _ ε hε (IsSemiAbelian.pullback (ξ ≫ f) G hG) _ (h V hV hf (ξ ≫ f) hξ')
  refine ⟨D, A, U, LBIso.trans U.LG.isLB (LB.isLB_pull (LB.isLB_pull L.isLB _) _)
    (LB.isLB_pull (bL L f).isLB _) hU ?_⟩
  exact LBIso.chartPull (h := ε.hom.left)
    (chartPullLinComb L.L _ (fun _ : PUnit => ε.hom.left) (fun _ => pullback.fst G.hom (ξ ≫ f)) (fun _ => 1) _ fun _ => rfl)
    (chartPullLinComb L.L _ (fun _ : PUnit => pullback.fst (bG G f).hom ξ) (fun _ => pullback.fst G.hom (ξ ≫ f))
      (fun _ => 1) _ fun _ => hφ.symm)
    (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))

theorem unifAlong_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW hG h => unifAlong_bG G L hW.fromSpec hG h

end GlobalTheory.KeyVals

end
end

