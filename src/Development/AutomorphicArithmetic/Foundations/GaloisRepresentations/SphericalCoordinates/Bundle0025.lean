import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3288
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fixEq_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixEq := by
  intro hHC hOne hLat p _ D G L gb N N' h hLev X X' c₁ c₂ hX hL hX' hL' ρ hFine v t₀ B PD RD D' t hCls P j a hCo y hSees ga hga P₁ P₂ x₁ x₂ e₁ e₂ hU₁ hU₂ hP
  have hN3 : 3 ≤ N := hLev.1
  have hNp : N.Coprime p := hLev.2.1
  have hdvd : N ∣ N' := hLev.2.2.2.2.1
  obtain ⟨hPl, hCA, hLoc, -⟩ := hCo
  obtain ⟨-, hS1, hS2⟩ := hSees
  obtain ⟨D'', t'', P'', e'', inc, j'', hCls'', hU'', hPinc, he'', hd, hjinc, hPl'', hCA'', hLoc''⟩ :=
    hHC p D G L gb N N' h hLev X X' c₂ hX hL hX' hL' ρ hFine D' t P₁ x₁ e₁ hU₁ B j a.1.1 (PD.lat a.1.2) hPl hCA hLoc
  obtain ⟨e₂', hU₂', he₂'⟩ :=
    hOne p D G L gb N N' h hLev X X' c₁ hX hL hX' hL' ρ hFine B PD D' t hCls j a.1 hPl hCA hLoc P₂ x₂ e₂ hU₂
  have hCAN : IsCoordA L (trivX B) N D' t j a.1.1 := by
    refine ⟨hCA.1, fun b => ?_⟩
    obtain ⟨w, hw, hweq⟩ := hCA.2 b
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k • w, AddSubgroup.nsmul_mem _ hw k, ?_⟩
    rw [hweq, hk, mul_smul]
  have hmem1 : (a.1.1 * h⁻¹)⁻¹ * B.toAf y * a.1.1 ∈ L.KN N := by
    have hS1' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS1
    rw [mul_inv_rev, inv_inv]
    rw [mul_assoc h, mul_assoc h]
    exact hS1'
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B PD N (by omega) hNp D'' t'' D' t j'' j (a.1.1 * h⁻¹, a.1.2) a.1 N N' t'' t
      hCls'' hCls hPl'' hPl hCA'' hCAN hLoc'' hLoc y).mp ⟨hmem1, hS2⟩
  have hcancel : ∀ w' : VQ D, (actY L y) ((actY L y⁻¹) w') = w' := by
    intro w'
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hgi : ∀ u, w (ga u) = inc u := by
    intro u
    apply hPl''.1
    rw [hjinc, hwj, hga, hcancel]
  have hPw : ∀ x, P'' (w x) = P₂ x := by
    intro x
    obtain ⟨d, u, hd0, hdu⟩ := hd (w x)
    have hgu : ga u = d • x := by
      apply w.injective
      rw [hgi, hdu, map_nsmul]
    have h2 : d • P'' (w x) = d • P₂ x := by
      rw [← map_nsmul, ← map_nsmul, ← map_nsmul, ← hgu, hgi, hPinc, hP]
    exact smul_right_injective _ hd0 h2
  have hPw' : ∀ x, P'' (w x) = (LinearEquiv.refl ℂ (Fin D.g → ℂ)) (P₂ x) := fun x => hPw x
  have hpt : x₂ ≫ c₁.q = x₁ ≫ c₂.q :=
    hFine.sep D' D'' t t'' P₂ P'' _ _ e₂' e'' hU₂' hU'' w (LinearEquiv.refl ℂ _) hwm hPw'
  have hT := GlobalTheory.T.uniformisationAt_transport_isometry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w (LinearEquiv.refl ℂ _) (by omega) hU₂' hwm hPw' hU''.2.1
  have key : ∀ (y₁ y₂ : Sp ℂ ⟶ (gfam X.univ hX hL).X) (hy : y₁ = y₂)
      (f₁ : (Fin D.g → ℂ) → (Over.mk y₁ ⟶ (gfam X.univ hX hL).A))
      (f₂ : (Fin D.g → ℂ) → (Over.mk y₂ ⟶ (gfam X.univ hX hL).A)),
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₁ f₁ →
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₂ f₂ →
      ∀ z, Over.Hom.left (f₁ z) = Over.Hom.left (f₂ z) := by
    intro y₁ y₂ hy f₁ f₂ h₁ h₂ z
    subst hy
    rw [GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking _ _ _ _ _ _ _ _ _ _ _ _ _ f₁ f₂ hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D'' t'' hCls'') h₁ h₂]
  refine ⟨hpt.symm, fun z => ?_⟩
  rw [← he'' z, ← he₂' z]
  exact key _ _ hpt.symm e'' _ hU'' hT z
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem kap_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (v : InfinitePlace G.F)
    (t₀ : D.F →+* ℂ) (z : ℂ) : kap L v t₀ z⁻¹ = (kap L v t₀ z)⁻¹ := by
  unfold kap
  split_ifs <;> simp

theorem UpperTheory.Gal.W2.fixLoc_of :
    UpperTheory.Gal.W2.SheetOf → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.PowCorr → UpperTheory.Gal.W2.CspDim → UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.EigTop → UpperTheory.Gal.W2.LocSum → UpperTheory.Gal.W2.RegSep → UpperTheory.Gal.W2.InvMin → UpperTheory.Gal.W2.MinBridge → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.FixLoc := by
  intro hSheet hFixGa hFixEq hOneAt hPow hCsp hAd hEig hLoc hRegSep hInvMin hMinB hChart hPt
  intro p _ D G L ha hm v hv t₀ ht gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig hsm hreg U B PD RD i P j a hper hco y hsees k α hα h₁ h₂
  have hFM : FullMark N' (U.Di i) (U.t i) := by
    obtain ⟨⟨f, ν, hft, -, hn⟩, -⟩ := U.mem i
    intro x
    obtain ⟨a', e', hx⟩ := (hn N' (by have := hlev.2.2.1; omega) hlev.2.2.2.1).2.2.2.1 x
    exact ⟨a', e', by rw [hft]; exact hx⟩
  obtain ⟨S, hSu, hSex⟩ := hSheet D.O D.inv D.g ρ D.La (gfamD X' hX' hL') N' (D.Cls N') U i hlev.2.2.1 hFM
  have hUA := U.unif i P hper
  obtain ⟨ga, H, hga, hfix, hHQ⟩ := hFixGa p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P) hUA y hsees
  obtain ⟨Hm, hHm1, hHm2, hHm3⟩ := hper.2.2.2.2
  have hHerm : IsHermOf (U.Di i) P Hm := ⟨hHm1, hHm2, hHm3⟩
  obtain ⟨co, hcoC⟩ := hCsp D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm
  obtain ⟨hHdet, hHcomm, hHCsp⟩ := hAd D.O D.inv D.g ρ (U.Di i) P Hm hper hHerm ga H hfix
  let φ : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin D.g) (Fin D.g) ℂ :=
    (LinearMap.mulRight ℂ (H.map star)⁻¹ ∘ₗ LinearMap.mulLeft ℂ H) ∘ₗ co
  have hφ : ∀ b, φ b ∈ LinearMap.range co := by
    intro b
    rw [hcoC.2]
    exact hHCsp _ (by rw [← hcoC.2]; exact LinearMap.mem_range_self co b)
  let eco := LinearEquiv.ofInjective co hcoC.1
  let T : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Fin (D.n - 1) → ℂ :=
    eco.symm.toLinearMap ∘ₗ φ.codRestrict (LinearMap.range co) hφ
  have hT : ∀ b, co (T b) = H * co b * (H.map star)⁻¹ := by
    intro b
    have h2 := congrArg Subtype.val (eco.apply_symm_apply ⟨φ b, hφ b⟩)
    simpa [T, φ, eco, LinearEquiv.ofInjective_apply] using h2
  obtain ⟨Q, hQper, hQP, hQrel⟩ := hco.2.2.2
  have hfixL := hsees.1
  set lam := RootSumWeights.eigL G v B.β y a.2.1 with hlam
  have hlamspec : (LKCx.toV G v B.β y).val *ᵥ a.2.1 = lam • a.2.1 := by
    rw [hlam]
    simp only [RootSumWeights.eigL, dif_pos hfixL]
    exact hfixL.choose_spec
  have hne : a.2.1 ≠ 0 := by
    intro h0
    have := a.2.2
    rw [h0] at this
    simp at this
  have hinvmul : (LKCx.toV G v B.β y⁻¹).val * (LKCx.toV G v B.β y).val = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hback : (LKCx.toV G v B.β y⁻¹).val *ᵥ (lam • a.2.1) = a.2.1 := by
    rw [← hlamspec, Matrix.mulVec_mulVec, hinvmul, Matrix.one_mulVec]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne
    rw [← hback, h0, zero_smul, Matrix.mulVec_zero]
  have hinvspec : (LKCx.toV G v B.β y⁻¹).val *ᵥ a.2.1 = lam⁻¹ • a.2.1 := by
    rw [Matrix.mulVec_smul] at hback
    rw [← hback, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    exact hback.symm ▸ rfl
  have hmark := RD.mark y⁻¹ Q a.2 H lam⁻¹ hQper hQrel (fun w => hHQ w Q hQP hQper) hinvspec
  rw [kap_inv] at hmark
  have hcy : ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) = (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) := by
    simp [Subgroup.coe_inv, Prod.fst_inv]
  have hmin := hMinB p D G L B.β (U.Di i) j hco.1 ga ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) (fun u => hga u)
  rw [hcy] at hmin
  obtain ⟨hIv, hIdeg, hIsep⟩ := hInvMin G.F G.C ((↑y : G.Cˣ × ℚˣ).1)
  obtain ⟨hRdeg, hRsep⟩ := hRegSep p D G L v hv B a y hsees.1 (hreg _ hsees.2.1)
  have hdeg : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).natDegree = D.n := by
    rw [Polynomial.natDegree_map, hIdeg, hRdeg, L.n_eq]
  have hsep : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).Separable :=
    (hIsep hRsep).map
  obtain ⟨-, hEall⟩ := hEig D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm ga H hfix _ hmin hdeg hsep (D.n - 1) co hcoC T hT k α hα
  obtain ⟨-, hdetT, hdetF, hform⟩ := hEall _ hmark
  have hact : ∀ P' : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P' → ∀ (b : D.O) (z : Fin D.g → ℂ),
      Over.Hom.left (S.ex P' (ρ b *ᵥ z)) = Over.Hom.left (S.ex P' z) ≫ Over.Hom.left (X'.univ.act.act b) := by
    intro P' hP' b z
    rw [hSex, hSex, (U.unif i P' hP').2.2.2.2.1 b z, Over.comp_left]
    rfl
  have hEq : ∀ P₁ P₂ : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P₁ → PELU.IsPeriod (U.Di i) ρ P₂ →
      (∀ u, P₂ (ga u) = P₁ u) →
        S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧
          ∀ z : Fin D.g → ℂ, Over.Hom.left (S.ex P₁ z) ≫ c₂.tot = Over.Hom.left (S.ex P₂ z) ≫ c₁.tot := by
    intro P₁ P₂ h1 h2 h12
    obtain ⟨hq, hz⟩ := hFixEq p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco y hsees ga hga P₁ P₂ (U.u i P₁) (U.u i P₂) (U.ex i P₁) (U.ex i P₂) (U.unif i P₁ h1) (U.unif i P₂ h2) h12
    refine ⟨by rw [hSu, hSu]; exact hq, fun z => by rw [hSex, hSex]; exact hz z⟩
  obtain ⟨hCorr, hInjP⟩ := hPow p D G L gb N N' h X X' c₁ c₂ ρ (U.Di i) S hact ga hEq k α
  obtain ⟨e₁, hUA1, he₁⟩ := hOneAt p D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hfine B PD (U.Di i) (U.t i) (U.mem i) j a.1 hco.1 hco.2.1 hco.2.2.1 P (U.u i P) (U.ex i P) hUA
  have hker : ∀ z z' : Fin D.g → ℂ, Over.Hom.left (S.ex P z) ≫ c₁.tot = Over.Hom.left (S.ex P z') ≫ c₁.tot → z - z' ∈ P.range := by
    intro z z' hzz
    rw [hSex, hSex] at hzz
    have hee : e₁ z = e₁ z' := Over.OverMorphism.ext (by rw [he₁ z, he₁ z']; exact hzz)
    have hsplit : e₁ z = e₁ z' * e₁ (z - z') := by rw [← hUA1.2.2.1.1, add_sub_cancel]
    rw [hee] at hsplit
    exact (hUA1.2.2.2.1 (z - z')).1 (mul_eq_left.mp hsplit.symm)
  have hinj := hInjP P hper hker
  have hrange : ∀ z : Fin k → Fin D.g → ℂ, (∀ s, z s ∈ P.range) →
      ∀ s, (fibMap H (diagAct (algebraMap (𝓞 D.F) D.O) ρ α)) z s ∈ P.range := by
    intro z hz s
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (hz s)
    refine AddMonoidHom.mem_range.mpr ⟨ga (algebraMap (𝓞 D.F) D.O (α s) • x), ?_⟩
    rw [hfix.2, hper.1, hx]
    simp [fibMap, diagAct, Matrix.toLin'_apply]
  obtain ⟨Fx, hFx, hAt⟩ := hLoc D.O D.inv D.g ρ (U.Di i) _ _ _ S (D.n - 1) hsm k _ (sZ X k) (c₁.pw k) (c₂.tw α) h₁ h₂ P Hm hper hHerm co hcoC ga H hfix T hT _ hCorr hrange hinj hdetT hdetF
  have hpc0 : perC P 0 = P := by
    ext x s
    simp [perC, PeriodCoord.realMap]
  have hpc1 : perC P (H * 0 * (H.map star)⁻¹) = P := by rw [mul_zero, zero_mul, hpc0]
  have hch := hChart _ _ _ ρ (U.Di i) _ _ _ S k _ (c₁.pw k) (c₂.tw α) P Hm hper hHerm ga H hfix _ hCorr 0
    (by rw [hpc0]; exact hper) (by rw [hpc1]; exact hper) 0
  rw [hpc0, hpc1, map_zero] at hch
  obtain ⟨hpt1, -, -, -, -⟩ := hPt _ _ _ ρ (U.Di i) _ _ _ S k P hper
  refine ⟨Fx, fun x => by have hx := hFx x; rw [hSu] at hx; exact hx, ⟨⟨S.pt k P 0, ?_⟩, (hFx _).2 ⟨hpt1 0, hch.symm⟩⟩, fun At hTan => ⟨(hAt At hTan).1, fun t => ?_⟩⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X'.s) (hpt1 0)).trans (S.ov P hper))
  · exact ((hAt At hTan).2 t).trans ((hform t).trans (by unfold wtFix; rw [hIv]))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PGUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem gUnif_of : ModelEx → GenCmp → GenPts → BaseC → GFine → GUnif := by
  intro hM hC hP hB hF p _ D ha hm t₀ ht ρ hρ gb hgb N hN hNp X
  obtain ⟨b, hbρ, hbt, hbT⟩ := hB p D ha hm t₀ ht ρ hρ gb hgb
  obtain ⟨M⟩ := hM p D ℂ b N hN hNp
  obtain ⟨j, hjo, hjc, hjs, hjG⟩ := hC p D ℂ b ℂ (RingHom.id ℂ) gb hbρ hbt N hN hNp M X
  have hpts := hP p D ℂ b (RingHom.id ℂ) gb hbρ hbt N hN hNp M X j hjo hjc hjs hjG
  obtain ⟨h, hL, -⟩ := model_uniformised p D ℂ b N (RingHom.id ℂ) ρ M hN hNp hbT
  have hfine := T.complexPoints_classify_markedPeriods p D ℂ b N (RingHom.id ℂ) ρ M h hL (by omega) hNp hbT
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by
    simp [spMap]
  have hsq : (j ≫ pullback.fst M.s (spMap (RingHom.id ℂ))) ≫ M.s = X.s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, hid, Category.comp_id]
  obtain ⟨hX, hL', hXf⟩ := hF p D b gb N M X ρ h hL _ hsq hjG hpts hfine
  haveI := hjo
  haveI := hjc
  have hsm : SmoothOfRelativeDimension (D.n - 1) X.s := by
    have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
    rw [ha, Nat.one_mul] at h1
    haveI : SmoothOfRelativeDimension (D.n - 1) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (D.n - 1)).of_isPullback
        (IsPullback.of_hasPullback _ _) h1
    have h3 : SmoothOfRelativeDimension (0 + (D.n - 1))
        (j ≫ pullback.snd M.s (spMap (RingHom.id ℂ))) := inferInstance
    rw [Nat.zero_add, hjs] at h3
    exact h3
  have hqc : QuasiCompact X.s := by
    haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
    rw [← hjs]
    infer_instance
  have hsep : IsSeparated X.s := by
    haveI : IsSeparated M.s := by
      obtain ⟨K, i, hi, -, hiK⟩ := M.qproj
      haveI := hi
      haveI := isProper_str ℂ K
      rw [← hiK]
      infer_instance
    rw [← hjs]
    infer_instance
  refine ⟨hsm, hqc, hsep, hX, hL', hXf, ?_⟩
  refine T.complexUniformisation_of_markedPeriods_family _ _ _ ρ _ (gfam X.univ hX hL') N (D.Cls N) (D.n - 1) hN ?_ hsm hqc
    (fun D' t ht => Datum.Cls.fullMark D N (by omega) hNp D' t ht) hXf
  intro a
  change X.univ.eta a ^ N = 1
  rw [← GObj.eta_nsmul, GObj.eta_ker]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem powerSeries_expansion_image_dense_with_denominator {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (z : AfP p ⊗[ℚ] VQ D) : ∃ (w : VQ D) (e : AfP p ⊗[ℚ] VQ D), e ∈ LaHat D ∧
      z = (1 : AfP p) ⊗ₜ[ℚ] w + N • e := by
  obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D z
  obtain ⟨x, e, he, hx⟩ := exists_inAf_add_nsmul_of_mem_laHat p D (t * N) (Nat.mul_pos ht0 hN)
    (Nat.Coprime.mul_left htc hNp) (t • z) ht
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ⟨(t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x), e, he, ?_⟩
  have h1 : t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x))) = inAf D x := by
    rw [inAf, ← Nat.cast_smul_eq_nsmul ℚ, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ ht', one_smul]
  have h2 : t • z = t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x)) + N • e) := by
    rw [hx, smul_add, h1, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ t, ← Nat.cast_smul_eq_nsmul ℚ t] at h2
  exact smul_right_injective _ ht' h2

theorem UpperTheory.Gal.W2.rdDense_of :
    UpperTheory.Gal.W2.RdDense := by
  intro p _ D G L x h₁ n hn z
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hTS : T * S = 1 := by
    have e1 : actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : L.actG h₁⁻¹ * L.actG h₁ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) *
      (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)), e1, _root_.one_mul, e2]
  obtain ⟨m, hm0, hmc, hm⟩ := DenEnd.exists_coprime_nsmul_map_mem p D T
  obtain ⟨k, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hn0 : 0 < n' := Nat.pos_of_ne_zero fun h => hn' (h ▸ dvd_zero p)
  have hnc : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn').symm
  obtain ⟨w, e, he, hz⟩ := powerSeries_expansion_image_dense_with_denominator D (n' * m) (Nat.mul_pos hn0 hm0) (Nat.Coprime.mul_left hnc hmc) (S z)
  have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k)) := fun u => by
    rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv u) k
  have hz2 : z = T (S z) := by
    rw [← Module.End.mul_apply, hTS]; rfl
  have hr : rd L x h₁ w = T ((1 : AfP p) ⊗ₜ[ℚ] w) := rfl
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨w, algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k) • (m • T e), DenEnd.smul_mem D hint (hm e he), ?_⟩
  rw [hr, hz2, hz, map_add, map_nsmul]
  congr 1
  rw [algebraMap_smul, hnn]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hpk : (p : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
  push_cast
  linear_combination (-((n' : ℚ) * m)) * hpk
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mul_unit_eq_algebraMap_mul {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (xs : S) (x : Sˣ) (b bi : S)
    (t : A) (hb : bi * b = 1) (hx : (x : S) * b * xs = algebraMap A S t) :
    xs * (x : S) = algebraMap A S t * bi := by
  have hc : ∀ y : S, algebraMap A S t * y = y * algebraMap A S t := fun y => Algebra.commutes t y
  have h1 : xs = bi * ((↑x⁻¹ : S) * algebraMap A S t) := by
    rw [← hx, ← _root_.mul_assoc (↑x⁻¹ : S), ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
      _root_.one_mul, ← _root_.mul_assoc, hb, _root_.one_mul]
  rw [h1, _root_.mul_assoc, _root_.mul_assoc, hc, ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
    _root_.one_mul]
  exact (hc bi).symm

theorem UpperTheory.Gal.W2.rdForm_of :
    UpperTheory.Gal.W2.RdForm := by
  intro p _ D G L B h₁
  obtain ⟨t, ht⟩ := B.trivAf.choose_spec
  have hx : (↑(trivX B) : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ↑B.β *
      MulOpposite.unop ((starT G.star (AfP p)) ↑(trivX B)) = algebraMap (AfP p) _ ↑t := ht
  have key := mul_unit_eq_algebraMap_mul (A := AfP p) _ (trivX B) _ (inC G (AfP p) ↑B.β⁻¹) _
    (by rw [← map_mul, Units.inv_mul, map_one]) hx
  have hsh : sh G (↑B.β⁻¹ : G.C) = ↑B.β⁻¹ := by
    have h : sh G (↑B.β⁻¹ : G.C) * ↑B.β = 1 := by
      rw [← B.sym]
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    exact Units.mul_eq_one_iff_eq_inv.mp h
  refine ⟨(h₁⁻¹).1.2 * t, fun u w => ?_⟩
  unfold rd
  rw [actG_form_eq_sim, adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, key, map_mul,
    AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [inC, AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  rw [actOn_tmul_tmul', TensorProduct.smul_tmul', LinearMap.BilinForm.baseChange_tmul, formB,
    L.adj, hsh, Units.val_mul]
  simp only [smul_eq_mul]
  rw [Algebra.smul_def]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PStabTriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.stabTriv_of :
    UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.Rigid → UpperTheory.Gal.W2.StabTriv := by
  intro hOcc hLat hFix hRig p _ D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N hN3 hNp B a y hSees
  obtain ⟨D', t, P, j, hCls, hPer, hPl, hCA, hLoc, Q, hQ, hQj, hrel⟩ :=
    hOcc p D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N (by omega) hNp B a
  obtain ⟨hFixL, hS1, hS2⟩ := hSees
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B (PD B) N (by omega) hNp D' t D' t j j a.1 a.1 N N t t
      hCls hCls hPl hPl hCA hCA hLoc hLoc y).mp ⟨hS1, hS2⟩
  obtain ⟨hiff, hinv⟩ := hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y
  obtain ⟨H, hH⟩ := hiff.mp hFixL
  obtain ⟨H', hH'⟩ := ((hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y⁻¹).1).mp (hinv hFixL)
  have hback : ∀ x : VQ D, (actY L y⁻¹) ((actY L y) x) = x := by
    intro x
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have key : ∀ z, (H' * H) *ᵥ z = z := by
    let f : (Fin D.g → ℂ) →ₗ[ℝ] (Fin D.g → ℂ) :=
      (Matrix.toLin' (H' * H)).restrictScalars ℝ - LinearMap.id
    have hle : Set.range Q ⊆ LinearMap.ker f := by
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show Matrix.toLin' (H' * H) (Q x) - Q x = 0
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hH x, ← hH', hback, sub_self]
    intro z
    have hz : z ∈ LinearMap.ker f := by
      have hs := Submodule.span_le.mpr hle
      rw [hQ.2.1] at hs
      exact hs Submodule.mem_top
    rw [LinearMap.mem_ker] at hz
    have hz' : Matrix.toLin' (H' * H) z - z = 0 := hz
    rwa [Matrix.toLin'_apply, sub_eq_zero] at hz'
  have hHH : H' * H = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact LinearMap.ext fun z => by rw [Matrix.toLin'_apply, key]; rfl
  letI : Invertible H := invertibleOfLeftInverse H H' hHH
  have hfix : ∀ u, w u = u :=
    hRig D.O D.inv D.g ρ D.La N D' t P w (Matrix.toLinearEquiv' H this) hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D' t hCls) hPer hwm
      (fun u => by
        rw [← hQj (w u), hwj, hH, hQj]
        show H *ᵥ P u = Matrix.toLin' H (P u)
        rw [Matrix.toLin'_apply])
  have hrep : L.rep ↑(↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, u, hm, hmu⟩ := hPl.2.2.1 x
    have h1 : m • (actY L y) x = m • x := by
      rw [← map_nsmul, hmu, ← hwj, hfix]
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hm) h1
  have hy1 : (↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply Units.ext
    apply L.rep_inj
    rw [hrep, Units.val_one, map_one]
  have hprop := y.2
  obtain ⟨hy, -⟩ := hprop
  rw [hy1] at hy
  have hsh : sh G (1 : G.C) = 1 := by simp [sh]
  rw [Units.val_one, _root_.one_mul, hsh, _root_.mul_one] at hy
  have hq : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    have : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) * ↑B.β = 1 * ↑B.β := by rw [_root_.one_mul, ← hy]
    exact (Units.mul_left_inj B.β).mp this
  have hq' : ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    rw [← map_one (algebraMap ℚ G.C)] at hq
    exact (algebraMap ℚ G.C).injective hq
  apply Subtype.ext
  exact Prod.ext hy1 (Units.ext hq')
end

