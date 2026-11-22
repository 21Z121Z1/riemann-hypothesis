import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCoeffAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.KS
open TrivSqZeroExt (inl inr)

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem exists_isTransl_snd {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {u : epsR K ⟶ A} (hu : IsTangent u)
    {dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hd : IsInvDer u dd) {S : Type} [CommRing S]
    (ψ : K →+* S) (x : Sp S ⟶ A.left) (hx : x ≫ A.hom = spMap ψ) :
    ∃ w, GlobalTheory.CechKS.IsTransl ψ x u w ∧ ∀ (O : A.left.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O) (f : Γ(A.left, O)),
      (valR w O f).snd = GlobalTheory.TangentOrigin.evalPt x O h (dd O f) := by
  letI : Algebra K (DualNumber S) := ((algebraMap S (DualNumber S)).comp ψ).toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ x) (by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl)
  let v' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (DualNumber.eps : DualNumber S) (by simp)) ≫ u
  have hv' : v'.left = spMap (dualMap ψ) ≫ u.left := by
    show Spec.map _ ≫ u.left = _
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    ext <;> simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, dualMap, Algebra.ofId_apply,
      RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨(v' * z).left, ⟨z, v', rfl, hv', by rw [mul_comm]⟩, fun O h f => ?_⟩
  have hz : ⊤ ≤ z.left ⁻¹ᵁ O := fun p _ => h (Set.mem_univ _)
  obtain ⟨h', H⟩ := GlobalTheory.InvFieldBasis.evalPt_translate hu hd (DualNumber.eps : DualNumber S) (by simp) z O hz
  have e1 : valR (v' * z).left O f = GlobalTheory.TangentOrigin.evalPt (v' * z).left O h' f := by
    rw [valR, dif_pos h']; rfl
  have e2 : ∀ s, GlobalTheory.TangentOrigin.evalPt z.left O hz s = inl (GlobalTheory.TangentOrigin.evalPt x O h s) := fun s =>
    GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap S (DualNumber S)) x O h hz s
  rw [e1, H, e2, e2]
  simp

theorem exists_polAV_interior {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (x0 : Sp K ⟶ Y.X)
    (hx : ⊤ ≤ x0 ⁻¹ᵁ GlobalTheory.LogKS.interior Y) :
    ∃ (P₀ : Out.PolAV (Sp K)) (θ : P₀.A.left ⟶ Y.t.G.left), IsGrpPullback P₀.A Y.t.G x0 θ ∧
      LBIso P₀.L (Y.t.PP.L.pull θ) := by
  have hr : Set.range x0 ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    exact hx (Set.mem_univ p)
  let y' := IsOpenImmersion.lift Y.j x0 hr
  have hy' : y' ≫ Y.j = x0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨P, φ, -, hφ, hL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Y.oF.t Y.oF.proper Y.oF.ample
    Y.oF.ktriv K y'
  have g1 : IsGrpPullback P.A Y.t.G (y' ≫ Y.j) (φ ≫ Y.m.φ) := hφ.comp Y.m.cart
  rw [hy'] at g1
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have i1 : LBIso (Y.oF.t.PP.L.pull φ) (Y.t.PP.L.pull (φ ≫ Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ φ φ rfl)
      (chartPullSame _ (fun _ => φ ≫ Y.m.φ) (fun _ => Y.m.φ) (fun _ => 1) φ (fun _ => rfl)) ⟨w, hw⟩
  exact ⟨P, φ ≫ Y.m.φ, g1, LBIso.trans P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL i1⟩

theorem valR_eq_evalPt {S : Type} [CommRing S] {Z : Scheme.{0}} (x : Sp S ⟶ Z) (O : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (s : Γ(Z, O)) : valR x O s = GlobalTheory.TangentOrigin.evalPt x O h s := by
  rw [valR, dif_pos h]; rfl

theorem eq_of_evalPt_eq {Z : Scheme.{0}} {O : Z.Opens} (s s' : Γ(Z, O))
    (h : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ O),
      GlobalTheory.TangentOrigin.evalPt x O hx s = GlobalTheory.TangentOrigin.evalPt x O hx s') : s = s' := by
  let J : Type := {V : Z.Opens // IsAffineOpen V ∧ V ≤ O}
  refine eq_of_rsT_eq (fun V : J => V.1) (fun V => V.2.2) (fun p hp => ?_) s s' fun V => ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp O.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hpV⟩
  obtain ⟨t, ht, et⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq V.2.1 (RingHom.id _)
  have ht' : ⊤ ≤ t ⁻¹ᵁ O := fun p hp => V.2.2 (ht hp)
  have e : ∀ a : Γ(Z, O), rsT a V.1 = GlobalTheory.TangentOrigin.evalPt t O ht' a := fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_res t V.2.2 ht' ht, et, rsT_of_le V.2.2]; rfl
  rw [e, e, h _ t ht']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

theorem pull_diff (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a))
    (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) {J : Type} (W : J → t.G.left.Opens) (j : J → t.PP.L.ι)
    (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hWj : ∀ i, W i ≤ t.PP.L.U (j i))
    (hdiff : ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O))
      (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, GlobalTheory.LogKS.IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d i O f - d i' O f) =
        ∑ a, ∑ b, φ (Θ a b) *
          ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) *
          (valR (w a) O f).snd)
    (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ t.G.left)
    (hm : IsGrpPullback A t.G x0 m) (u : Fin n → (epsR K ⟶ A))
    (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ v a)
    (dd : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ t.PP.L.U i)) (hφ : IsDlog m t.PP.L dd φ)
    (i i' : J) (O : t.G.left.Opens) (hO : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)) :
    (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn A.hom _ (GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) *
        dd a _ ((m.app O).hom f) := by
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.CechKS.isTangent_of_fibre t U v hv x0 hU A m u hm hu
  have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (hO hp).1, hWj i' (hO hp).2⟩
  have hOg' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i') := m.preimage_mono hOg
  refine eq_of_evalPt_eq _ _ fun S _ x hx => ?_
  let ψ : K →+* S := (Spec.preimage (x ≫ A.hom)).hom
  have hxA : x ≫ A.hom = spMap ψ := (Spec.map_preimage (x ≫ A.hom)).symm
  choose w hw hw' using fun a => exists_isTransl_snd (hut a) (hdd a) ψ x hxA
  have hbase : (x ≫ m) ≫ t.G.hom = spMap (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ GlobalTheory.LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hxA, GlobalTheory.Cris.spMap_comp (GlobalTheory.FlagMod.ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  have key := hdiff i i' O hO f S (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) (x ≫ m) (fun a => w a ≫ m) hbase hx
    (fun a => GlobalTheory.CechKS.IsTransl.isTranslate_comp t x0 A m hm _ (v a) (u a) (hu a) ψ x hxA (w a) (hw a))
  have hxg : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) := fun p hp => hOg' (hx hp)
  have ev_g : ∀ b, (valR (w b ≫ m) _ (t.PP.L.g (j i) (j i')).val).snd *
      valR (x ≫ m) _ (t.PP.L.g (j i) (j i'))⁻¹.val =
      GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) := fun b => by
    have hp : ∀ (s : Γ(t.G.left, t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))),
        pbT m s (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) = (m.app _).hom s := fun s => by
      show pbT m s (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) = _
      rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
    have hxg' : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) := hxg
    have e1 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) := by
      have := congrArg (GlobalTheory.TangentOrigin.evalPt x _ hxg) (hφ b (j i) (j i'))
      rw [map_mul, hp] at this
      exact this
    have h0 : (m.app _).hom (t.PP.L.g (j i) (j i')).val * (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = 1 :=
      calc _ = GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val *
              (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) := (map_mul _ _ _).symm
        _ = 1 := by rw [h0]; exact map_one _
    have e3 : GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) := by
      rw [rsT_of_le hOg', GlobalTheory.TangentOrigin.evalPt_res x hOg' hxg hx]
    rw [GlobalTheory.CechKS.valR_comp_app, GlobalTheory.CechKS.valR_comp_app, hw' b _ hxg', valR_eq_evalPt _ _ hxg', e3]
    show GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) *
      GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = _
    rw [← e1]
    linear_combination (GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i'))) * e2
  rw [GlobalTheory.CechKS.valR_comp_app, valR_eq_evalPt _ _ hx] at key
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ev_g, GlobalTheory.CechKS.valR_comp_app (w a) m O f, hw' a _ hx, map_mul, GlobalTheory.TangentOrigin.evalPt_constFn,
    GlobalTheory.InvFieldBasis.evalPt_congr hxA ⊤ le_rfl le_rfl, GlobalTheory.TangentOrigin.evalPt_spMap]
  rfl

theorem coeff_id {A₀ : Over (Sp K)} [GrpObj A₀] {g : ℕ} {v : Fin g → (epsR K ⟶ A₀)}
    {dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)} (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S)
    (m : A₀.left ⟶ X) (H : IsPullback m A₀.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U)
    (W₀ : X.Opens) (hW₀ : W₀ ≤ p ⁻¹ᵁ U) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W))
    (hadd : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f')
    (hmul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f)
    (hrs : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W'))
    (hbase : ∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X), y ≫ m = m' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)),
      (∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f') →
      (∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m'.app W).hom f * d W f' + (m'.app W).hom f' * d W f) →
      (∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m' ⁻¹ᵁ W')) →
      (∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' e d h1 h2 h3 h4
    subst e
    exact existsUnique_coeff hs hv hd x₀ p m H hU y W₀ hW₀ d h1 h2 h3 h4
  have := key (𝟙 _) m (Category.id_comp _) d hadd hmul hrs hbase
  simpa only [GlobalTheory.KS.LinDir.pbT_id] using this

theorem app_resG {Y Z : Scheme.{0}} (m : Y ⟶ Z) {W W' : Z.Opens} (h : W' ≤ W) (s : Γ(Z, W)) :
    (m.app W').hom (resG Z h s) = rsT ((m.app W).hom s) (m ⁻¹ᵁ W') := by
  have e : ∀ {O : Z.Opens} (s : Γ(Z, O)), (m.app O).hom s = pbT m s (m ⁻¹ᵁ O) := fun s => by
    rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
  rw [e, e, ← rsT_of_le h, pbT_rsT m h le_rfl, rsT_pbT m le_rfl (m.preimage_mono h)]

theorem field_base {X Z : Scheme.{0}} (π : Z ⟶ X) {U : X.Opens} (W₀ : Z.Opens) (hW₀ : W₀ ≤ π ⁻¹ᵁ U)
    (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hf : GlobalTheory.LogKS.IsField W₀ d) (D : Γ(X, U) → Γ(X, U))
    (hl : ∀ (h : W₀ ≤ π ⁻¹ᵁ U) (r : Γ(X, U)), d W₀ ((π.appLE U W₀ h).hom r) = (π.appLE U W₀ h).hom (D r)) :
    ∀ W, W ≤ W₀ → ∀ r, d W (pbT π r W) = pbT π (D r) W := by
  intro W hW r
  have e : ∀ s : Γ(X, U), pbT π s W = resG Z hW (pbT π s W₀) := fun s => by
    rw [← rsT_of_le hW, rsT_pbT π hW₀ hW]
  rw [e, e, hf.2.2 W₀ W hW le_rfl, pbT_of_le π hW₀, pbT_of_le π hW₀, hl hW₀]

theorem isCoc_lc {Y : Scheme.{0}} {I : Type} {Uc : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ} (c : Fin g → K)
    (φ : Fin g → C1 Uc) (h : ∀ a, IsCoc Uc (φ a)) : IsCoc Uc (lc q c φ) := by
  intro i j k
  simp only [lc, rsT_sum, rsT_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_constFn q (O₀ := Uc i ⊓ Uc j) inf_le_left,
    rsT_constFn q (O₀ := Uc j ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.2, h.2⟩),
    rsT_constFn q (O₀ := Uc i ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.1, h.2⟩), ← mul_add, h a i j k]

theorem constFn_sub {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (x y : K) :
    constFn q O (x - y) = constFn q O x - constFn q O y := by
  simp [constFn]

end GlobalTheory.KSUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponentialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  first | exact @GlobalTheory.exists_riemannForm_of_relAmple | exact GlobalTheory.exists_riemannForm_of_relAmple | (intros; apply GlobalTheory.exists_riemannForm_of_relAmple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  first | exact @GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel | exact GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel | (intros; apply GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingCom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

theorem GlobalTheory.FormalAlg.exists_projective_of_formal_embedding : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j)) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e)) → F ∈ vanIdeal B.hom s' := by
  intro V _ _ I hc Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V I (e + 1) = (Y e).hom ≫ thick V I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e => vanIdeal ((Y e).hom ≫ thick V I e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V I e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneous_correction_next_thickening V I Y β hβ H v hH n s hs hva
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => (mem_vanIdeal _ _ _).2 (hB' t F hF h)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, hF₁, hK, hG⟩ := GlobalTheory.Degen.exists_form_limit_ideal V I hc _ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
      (fun e F hF h => ht₀ t ht e F hF h) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub]
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hG d)
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullbackTwistedSection_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  first | exact @GlobalTheory.TwFam.exists_isPullT | exact GlobalTheory.TwFam.exists_isPullT | (intros; apply GlobalTheory.TwFam.exists_isPullT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLifts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
theorem secLift_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (a.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a h)).op).hom ((a.app U).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem secLift_comp_app {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) :
    ((a ≫ f).app U).hom x = (a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x) := by
  simp [Scheme.Hom.comp_app]
  rfl

theorem secLift_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (k : ℤ))).g i j).val =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) j 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (j 0))).hom (L.g (i 0) (j 0)))) ^ k := by
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl
theorem secLift_rr {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secLift_res_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Z.Opens}
    (h : V ≤ (a ≫ f) ⁻¹ᵁ U) (h' : V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U)) (x : Γ(X, U)) :
    (Z.presheaf.map (homOfLE h).op).hom (((a ≫ f).app U).hom x) =
      (Z.presheaf.map (homOfLE h').op).hom ((a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x)) := by
  rw [secLift_comp_app]
  rfl
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secLift_compat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (s : SecK L φ k) (i i' : Fin 1 → L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (s.f i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (s.f i') := by
  have h := s.compat i i'
  rw [secLift_g] at h
  exact h

def secLift_ofCompat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (σf : ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (K := Fin 1) (fun _ => φ) i))
    (h : ∀ i i' : Fin 1 → L.ι, (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (σf i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (σf i')) :
    SecK L φ k where
  f := σf
  compat i i' := (h i i').trans (congrArg (· * _) (secLift_g L φ k i i').symm)

set_option maxHeartbeats 1000000 in
theorem secK_lift_of_local_lift : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  intro X X' Y L f a α e k hinj s n j W hWtop hW hloc
  subst e
  have step1 : ∀ j' : Fin 1 → L.ι, ∃ y : Γ(X', LB.wchart L (K := Fin 1) (fun _ => f) j'),
      (a.app _).hom y = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a (a ≫ f) rfl j')).op).hom (s.f j') := by
    intro j'
    refine GlobalTheory.T.exists_preimage_of_local_preimages_injective a hinj _ W (by rw [hWtop]; exact le_top) _ ?_
    intro b
    obtain ⟨y, hy⟩ := hloc b
    have h1 : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ f ⁻¹ᵁ (L.U (j' 0) ⊓ L.U (j b)) :=
      fun x hx => ⟨LB.wchart_le L (K := Fin 1) (fun _ => f) j' 0 hx.1, hW b hx.2⟩
    refine ⟨(X'.presheaf.map (homOfLE h1).op).hom ((f.app _).hom (L.g (j' 0) (j b))) ^ k *
      (X'.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ W b)).op).hom y, ?_⟩
    have hc2 := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b) ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) j' ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) (fun _ => j b) from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl j' hx.1, extLI_le_chart L f a (a ≫ f) rfl (W b) (j b) (hW b) hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s j' (fun _ => j b))
    rw [map_mul, map_pow] at hc2
    erw [secLift_rr, secLift_rr, secLift_rr] at hc2
    rw [map_mul, map_pow, secLift_app_res, secLift_app_res, hy]
    erw [secLift_rr, secLift_rr]
    rw [hc2]
    exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f _ _ _ _).symm
  choose σf hσ using step1
  refine ⟨secLift_ofCompat L f k σf fun i i' => ?_, hσ⟩
  apply hinj (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i')
  have hG : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i 0))
      (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i' 0))
  have e1 := secLift_app_res a (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i) (σf i)
  have e2 := secLift_app_res a hG ((f.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))
  have e3 := secLift_app_res a (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i') (σf i')
  rw [map_mul, map_pow, e1]
  erw [e2, e3]
  rw [hσ, hσ]
  erw [secLift_rr, secLift_rr]
  have hc := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i') ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i' from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl i hx.1, extLI_le_wchart L f a (a ≫ f) rfl i' hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s i i')
  rw [map_mul, map_pow] at hc
  erw [secLift_rr, secLift_rr, secLift_rr] at hc
  rw [hc]
  exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f (L.U (i 0) ⊓ L.U (i' 0)) _ _ _)
end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realisedThetaSystem_of_universalSectionBasis : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.R = R ∧ ρ.n = n ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) := by
  first | exact @GlobalTheory.ThetaSBasis.exists_real_of_secBasis | exact GlobalTheory.ThetaSBasis.exists_real_of_secBasis | (intros; apply GlobalTheory.ThetaSBasis.exists_real_of_secBasis <;> assumption)
end

