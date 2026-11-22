import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0176
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrame
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.CongrOrbit

set_option maxHeartbeats 4000000 in

theorem exists_congr_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx
  have hx' : lact γ x ∈ (U.X k).dom := dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)

  let b₁ : Frame (U.X k).Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hm₁ : ∀ τ, mat b₁ τ = 1 := fun τ => rfl
  have hb₁ : b₁ ∈ Bor (U.X k).Ψ r := fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by
    have := hm₁ τ
    change Matrix.of (b₁ τ) = 1 at this
    have h2 := congrFun (congrFun this a) c
    simpa [Matrix.one_apply_ne (ne_of_gt hca)] using h2⟩
  have hrm : rmul (lact γ x) b₁ = lact γ x := by
    funext τ
    change mat (lact γ x) τ * mat b₁ τ = lact γ x τ
    rw [hm₁, Matrix.mul_one]
    rfl
  obtain ⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩) :=
    (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩
  obtain ⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k ⟨lact γ x, hx'⟩
  have hu : F.u (ik k) P' = F.u (ik k) P := by rw [← hPx, ← hPx', hB.1]
  obtain ⟨h, gam, hex, hh, hiso, hM, -⟩ := GlobalTheory.T.familyUnif_exp_unique_alt E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu

  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := F.t_surj (ik k) b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'

  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ)
      (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)
    have d0 := hv' τ i
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  let gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := (φ k).symm ≪≫ₗ gam ≪≫ₗ φ k
  let A : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ i j =>
    if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0
  have hA0 : ∀ τ i j, j < i → A τ i j = 0 := by
    intro τ i j hji
    simp only [A]
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  have hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
        ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j := by
    intro τ i hi v
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP', Equiv.apply_symm_apply]
    simp only [A]
    rw [dif_pos ⟨hi, j.2⟩]
    rfl
  have hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E)
      (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E)) := by
    intro u v
    obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]

  obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso
  have hε : ε = 1 := mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)
  have hUS : IsUStab (U.X k).Gm (U.X k).Λ η := ⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩
  have hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ,
      (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y := by
    intro w hw
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨w, hw⟩
    obtain ⟨e₀, he₀⟩ := f₁ a
    refine ⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩
    have h1 := hav ⟨w, hw⟩
    have h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀ := by
      simp only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add, map_nsmul]
    rw [h2] at h1
    change (η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1
    rw [h1]
    simp [Nat.cast_smul_eq_nsmul]

  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  let ρe := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ := ρe.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j :=
    fun τ i hi v hv => by
      have := hAr (ρe.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  obtain ⟨b, hb, hxb, -⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS)
    (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ))
    (fun τ => hA0 _) hrel
  exact ⟨η, hUS, hcong, b, hb, hxb⟩

end GlobalTheory.CongrOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDescentFlatSurjectiveQuasiCompact
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.LocDescent

theorem gs_comp_stalkMap {W Z Y : Scheme.{0}} (x : W ⟶ Z) (g : Z ⟶ Y) (w : W) (U : Y.Opens) (h : g (x w) ∈ U)
    (a : Γ(Y, U)) : gs (x ≫ g) w U a = (x.stalkMap w).hom (gs g (x w) U a) := by
  exact (gs_eq (x ≫ g) w U h a).trans (((Scheme.Hom.germ_stalkMap_apply x (g ⁻¹ᵁ U) w h _).symm).trans
    (congrArg (x.stalkMap w).hom (gs_eq g (x w) U h a).symm))

theorem stalkMap_fromSpecStalk_injective {Z : Scheme.{0}} (z : Z) :
    Function.Injective ((Z.fromSpecStalk z).stalkMap (closedPoint (Z.presheaf.stalk z))).hom := by
  have e := Scheme.stalkClosedPointTo_fromSpecStalk z
  have h : Function.Injective (Scheme.stalkClosedPointTo (Z.fromSpecStalk z)).hom := by
    rw [e]
    exact (Iso.commRingCatIsoToRingEquiv _).injective
  exact Function.Injective.of_comp (f := (stalkClosedPointIso (Z.presheaf.stalk z)).hom.hom) h

theorem gs_appLE_top {Z Y : Scheme.{0}} (g : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) g z U (h trivial) a).trans (by rw [Category.id_comp]))

theorem gs_eq_of_local {Z Y : Scheme.{0}} (g₁ g₂ : Z ⟶ Y) (z : Z) (U : Y.Opens) (h₁ : g₁ z ∈ U) (h₂ : g₂ z ∈ U)
    (a : Γ(Y, U)) (h : gs (Z.fromSpecStalk z ≫ g₁) (closedPoint (Z.presheaf.stalk z)) U a =
      gs (Z.fromSpecStalk z ≫ g₂) (closedPoint (Z.presheaf.stalk z)) U a) : gs g₁ z U a = gs g₂ z U a := by
  have e : Z.fromSpecStalk z (closedPoint (Z.presheaf.stalk z)) = z := Scheme.fromSpecStalk_closedPoint
  have H : ∀ y : Z, y = z → gs g₁ y U a = gs g₂ y U a → gs g₁ z U a = gs g₂ z U a := by
    rintro _ rfl h
    exact h
  have m : ∀ (g : Z ⟶ Y) (y : Z), y = z → g z ∈ U → g y ∈ U := by
    rintro g _ rfl h
    exact h
  exact H _ e (stalkMap_fromSpecStalk_injective z ((gs_comp_stalkMap _ g₁ _ U (m g₁ _ e h₁) a).symm.trans
    (h.trans (gs_comp_stalkMap _ g₂ _ U (m g₂ _ e h₂) a))))

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_sec_descend : ∀ {X B H : Scheme.{0}} (L : LB X), L.IsLB → ∀ (q : H ⟶ B), Flat q → Surjective q → QuasiCompact q → ∀ {K : Type} [Fintype K] (ψ : K → (B ⟶ X)) (ε : K → ℤ) (σ : LB.Sec (LB.LinComb L (fun k => q ≫ ψ k) ε)), (∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ H), g₁ ≫ q = g₂ ≫ q → ∀ J, Good L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J) → ∃ b : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) J, Good L z J → sval σ r z J = sval b (r ≫ q) z J := by
  intro X B H L hL q _ _ _ K _ ψ ε σ hσ
  have le : ∀ j : K → L.ι, q ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => q ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(B, LB.wchart L ψ j),
      (q.app _).hom a = (H.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine FunDescent.exists_app_eq q _ _ fun Z g₁ g₂ h₁ h₂ hq => fn_ext fun z _ => ?_
    rw [gs_appLE_top, gs_appLE_top]
    refine gs_eq_of_local g₁ g₂ z _ (h₁ trivial) (h₂ trivial) _ ?_
    have key : ∀ (S : Type) [CommRing S] [IsLocalRing S] (k₁ k₂ : Sp S ⟶ H), k₁ ≫ q = k₂ ≫ q →
        k₁ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j → k₂ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j →
        gs k₁ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) =
        gs k₂ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) := by
      intro S _ _ k₁ k₂ hk hz' hz
      choose J hJ using fun χ : Sp S ⟶ X => exists_chart hL (χ (closedPoint S))
      have hJ' : Good L (Z := Sp S) (closedPoint S) J := hJ
      refine (gs_res _ _ (le j) hz' _).trans (Eq.trans ?_ (gs_res _ _ (le j) hz _).symm)
      refine (sec_trans σ _ _ (le j hz') (hJ'.mem _ _)).trans
        (Eq.trans ?_ (sec_trans σ _ _ (le j hz) (hJ'.mem _ _)).symm)
      refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hσ S k₁ k₂ hk J hJ')
      refine (trF_comp _ _ _ _ _ _ _).trans (Eq.trans ?_ (trF_comp _ _ _ _ _ _ _).symm)
      simp only [← Category.assoc, hk]
    exact @key (Z.presheaf.stalk z) _ (Z.toLocallyRingedSpace.isLocalRing z)
      (Z.fromSpecStalk z ≫ g₁) (Z.fromSpecStalk z ≫ g₂)
      ((Category.assoc _ _ _).trans ((congrArg (Z.fromSpecStalk z ≫ ·) hq).trans (Category.assoc _ _ _).symm))
      (h₁ trivial) (h₂ trivial)
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z), q (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ q) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => q ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective q (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ => ?_⟩
  · have hy' : q y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) q y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) q y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ q) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ q) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ q) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine Eq.symm ?_
    rw [sval_of _ (r ≫ q) z J (fun a => J (r ≫ q ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ q ≫ ψ a))

end GlobalTheory.LocDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfRankOne
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM Polynomial

theorem dvd_of_smul_end_eq_smul {R M : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] (f : Module.End R M) {a b : R} (ha : a ≠ 0)
    (h : ∀ x, a • f x = b • x) {x₀ : M} (hx₀ : x₀ ≠ 0) : a ∣ b := by
  obtain ⟨P, hP, hf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (i : ℕ) (x : M), a ^ i • (f ^ i) x = b ^ i • x := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ f, Module.End.mul_apply, pow_succ' a, mul_smul, ih, smul_comm, h, pow_succ, mul_smul]
  have h0 : (P.scaleRoots a).eval b = 0 := by
    have h1 : (P.scaleRoots a).eval b • x₀ = a ^ P.natDegree • (aeval f P) x₀ := by
      rw [eval_eq_sum_range, aeval_eq_sum_range, natDegree_scaleRoots, Finset.sum_smul, LinearMap.sum_apply,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [coeff_scaleRoots, mul_smul, ← hpow, LinearMap.smul_apply, smul_smul, smul_smul, mul_assoc,
        pow_sub_mul_pow a hi', mul_comm]
    rw [hf, LinearMap.zero_apply, smul_zero, smul_eq_zero] at h1
    exact h1.resolve_right hx₀
  let K := FractionRing R
  have ha' : algebraMap R K a ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hc : algebraMap R K a * (algebraMap R K b / algebraMap R K a) = algebraMap R K b :=
    mul_div_cancel₀ _ ha'
  have hint : _root_.IsIntegral R (algebraMap R K b / algebraMap R K a) := by
    refine ⟨P, hP, ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := P) (algebraMap R K) (algebraMap R K b / algebraMap R K a) a
    rw [hc, eval₂_at_apply, h0, map_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (pow_ne_zero _ ha')
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨g, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hg, hc]

theorem exists_smul_of_rank_one (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (h : D.p + D.q = 1) (γ : D.La →+ D.La) (hγ : ∀ (s : 𝓞 E) (x : D.La), γ (s • x) = s • γ x) :
    ∃ g : 𝓞 E, ∀ x, γ x = g • x := by
  have := D.fin
  have := D.proj
  have hr : Module.finrank (𝓞 E) D.La = 1 := D.rank.trans h
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : D.La)
  obtain ⟨a, b, ha, hab⟩ := CMLat.exists_smul_eq_smul hr hx₀ (γ x₀)
  have key : ∀ x, a • γ x = b • x := fun x => by
    obtain ⟨r, s, hr0, e⟩ := CMLat.exists_smul_eq_smul hr hx₀ x
    have h1 : r • (a • γ x - b • x) = 0 := by
      rw [smul_sub, smul_comm r a, ← hγ, e, hγ, smul_comm a s, hab, smul_comm r b, e, smul_comm s b, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hr0)
  let f : Module.End (𝓞 E) D.La := { toFun := γ, map_add' := γ.map_add, map_smul' := hγ }
  obtain ⟨g, rfl⟩ := dvd_of_smul_end_eq_smul f ha key hx₀
  refine ⟨g, fun x => ?_⟩
  have h1 : a • (γ x - g • x) = 0 := by rw [smul_sub, key, mul_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left ha)

end GlobalTheory.FlatCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.GoodPlace

theorem ncard_primesOver_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 := by
  classical
  haveI := v.isMaximal
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E (p := v.asIdeal) v.ne_bot
  rw [h2] at hs
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 E) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q v.asIdeal (p : 𝓞 F)).1 hpv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ q := Ideal.map_le_iff_le_comap.2 (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).le
  have he : v.asIdeal.ramificationIdx' q = 1 := by
    by_contra hne1
    have h3 := (Ideal.ramificationIdx'_ne_one_iff hle).1 hne1
    have h4 := h3 (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hpv)
    rw [map_natCast] at h4
    exact (GlobalTheory.LocSplit.split_prime hp h q hpq).1 h4
  have hcF := (GlobalTheory.ColClassCompare.unram_card_of_split (F := F) (E := E) hp h v.asIdeal hpv).2
  have hcE := (GlobalTheory.ColClassCompare.unram_card_of_split (F := E) (E := E) hp h q hpq).2
  have hf : v.asIdeal.inertiaDeg' q = 1 := by
    have hcomap : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) q = v.asIdeal := (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).symm
    rw [Ideal.inertiaDeg', dif_pos hcomap]
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    have hfin : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ q) := inferInstance
    have := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ q)
    rw [hcF, hcE] at this
    exact (Nat.pow_right_injective hp.two_le (by simpa using this.symm))
  rw [he, hf]

end GlobalTheory.GoodPlace

namespace GlobalTheory.GoodPlace

theorem exists_good_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧
      SplitsFully D.host.E v₁ ∧ (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v₁) ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  intro D T L sc G μ₀ _ t P₀
  classical
  set S : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    P₀ ∪ (locPl G t).image (fun w => w.under (𝓞 D.host.F)) with hS
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  have hnot : ∀ u ∈ S, u ≠ v := by
    intro u hu e
    refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt u hp ?_ (e ▸ hv)
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  refine ⟨v, fun hv0 => hnot v (Finset.mem_union_left _ hv0) rfl, ?_,
    fun w hw e => hnot _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)) e, ?_⟩
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_first_order_deformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  first | exact @GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | exact GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective | (intros; apply GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPoints
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem compact_inter_ratPts_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)),
    IsCompact K → (K ∩ ratPts σ J).Finite := by
  intro F E _ _ _ _ _ σ n J K hK
  have hd : DiscreteTopology (ratPts σ J) := inferInstance
  have hcl : IsClosed ((ratPts σ J : Subgroup (GAd σ J)) : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  exact (hK.inter_right hcl).finite
    (IsDiscrete.mono (isDiscrete_iff_discreteTopology.2 hd) Set.inter_subset_right)

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatTorsionSubgroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_torsion_subgroup : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  first | (exact @GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (exact GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (intros; apply GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ lam : InfinitePlace E → DomWeight n, (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = dimW lam * ∏ᶠ w ∈ S, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) := by
  first | exact @GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | exact GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | (intros; apply GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallySmoothStalkUnitSmoothGroupSchemeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallySmooth_stalk_unit_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  first | exact @GlobalTheory.Nef.stalk_formallySmooth_of_smooth | exact GlobalTheory.Nef.stalk_formallySmooth_of_smooth | (intros; apply GlobalTheory.Nef.stalk_formallySmooth_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGermStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeUnitStalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  first | exact @GlobalTheory.Nef.stalkData_germ | exact GlobalTheory.Nef.stalkData_germ | (intros; apply GlobalTheory.Nef.stalkData_germ <;> assumption)
end

