import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0049
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.GObjMapCast
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem gObjMap_comp_φ {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁}
    {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f)
    (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

private theorem gObjMap_cast {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {f f' : S₁ ⟶ S₂} (e : f = f') (m : GObjMap o₁ o₂ f) : ∃ m' : GObjMap o₁ o₂ f', m'.φ = m.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem UpperTheory.Gal.G3.pPtEq :
    TransSelf → TransComp → TransPull → TransUniqPt → Rigid → PtEq := by
  intro hS hC hP hU hRg p _ D G L R _ _ gb N₁ N₂ N X₁ X₂ X h₁ h₂ g u π₁ Φ₁ π₂ Φ₂ w₁ w₂ i₁ i₂ a₁ a₂ hu he
    k _ _ s x y hx hy ox oy mx my θ hθ
  obtain ⟨e₁, o₁, ψ₁, f₁, t₁, rfl⟩ := w₁
  obtain ⟨e₂, o₂, ψ₂, f₂, t₂, rfl⟩ := w₂
  obtain ⟨o₁x, ⟨n₁⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s x hx o₁
  obtain ⟨o₂y, ⟨n₂⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s y hy o₂
  obtain ⟨ψ₁', t₁', c₁⟩ := hP p D G L R gb X₁.X (Sp k) X₁.s s x hx _ _ X₁.univ o₁ ox o₁x mx n₁ ψ₁ h₁ t₁
  obtain ⟨ψ₂', t₂', c₂⟩ := hP p D G L R gb X₂.X (Sp k) X₂.s s y hy _ _ X₂.univ o₂ oy o₂y my n₂ ψ₂ h₂ t₂
  have iu : Integ L u := UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have au : AdmK L N N u := fun v hv =>
    (L.KN N).mul_mem ((L.KN N).mul_mem hu hv) ((L.KN N).inv_mem hu)
  have t₃ := hC p D G L R gb (Sp k) s N₁ N₂ N ox oy o₂y θ ψ₂' g h₂ i₂ a₂ hθ t₂'
  have t₄ := hC p D G L R gb (Sp k) s N₁ N N ox o₂y o₂y (θ ≫ ψ₂') (𝟙 _) (h₂ * g) u iu au t₃
    ((hS p D G L R gb (Sp k) s N).1 o₂y u hu)
  rw [← he] at t₄
  obtain ⟨m, hm⟩ := hU p D G L R gb k s N₁ N ox o₁x o₂y ψ₁' _ h₁ i₁ a₁ t₁' t₄
  obtain ⟨A, hA⟩ := gObjMap_comp_φ n₁ f₁
  obtain ⟨B₀, hB₀⟩ := gObjMap_comp_φ n₂ f₂
  obtain ⟨B, hB⟩ := gObjMap_comp_φ m B₀
  have hxs : (x ≫ π₁) ≫ X.s = s := by rw [Category.assoc, e₁, hx]
  have hys : (𝟙 (Sp k) ≫ y ≫ π₂) ≫ X.s = s := by simp [Category.assoc, e₂, hy]
  have hxy : x ≫ π₁ = 𝟙 (Sp k) ≫ y ≫ π₂ :=
    (X.rep (Sp k) s o₁x).unique ⟨hxs, ⟨A⟩⟩ ⟨hys, ⟨B⟩⟩
  obtain ⟨B', hB'⟩ := gObjMap_cast hxy.symm B
  have hAB := hRg p D R gb X.X (Sp k) X.s s (x ≫ π₁) hxs N X.univ o₁x A B'
  refine ⟨by simpa using hxy, ?_⟩
  rw [hB', hB, hB₀, hA] at hAB
  calc mx.φ ≫ Over.Hom.left ψ₁ ≫ f₁.φ = (mx.φ ≫ Over.Hom.left ψ₁) ≫ f₁.φ := by rw [Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ n₁.φ ≫ f₁.φ := by rw [← c₁, Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ m.φ ≫ n₂.φ ≫ f₂.φ := by rw [hAB]
    _ = Over.Hom.left ((θ ≫ ψ₂') ≫ 𝟙 _) ≫ n₂.φ ≫ f₂.φ := by rw [← hm, Category.assoc]
    _ = Over.Hom.left θ ≫ (Over.Hom.left ψ₂' ≫ n₂.φ) ≫ f₂.φ := by simp
    _ = Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ₂ ≫ f₂.φ := by rw [c₂, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAdmOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem conj_core {V : Type*} [AddCommGroup V] [Module ℚ V] (H U Hi : V →+ V) {k N : ℕ} (hk : 0 < k) {v w : V}
    (hv : H (Hi v) = v) (e : U (k • Hi v) = k • Hi v + (N * k) • w) : H (U (Hi v)) = v + N • H w := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 := congrArg H e
  simp only [map_nsmul, map_add, hv] at h1
  have h2 : k • H (U (Hi v)) = k • (v + N • H w) := by
    rw [h1, smul_add, mul_comm N k, mul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ k, ← Nat.cast_smul_eq_nsmul ℚ k] at h2
  exact MulAction.injective₀ hk' h2

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {h u : G.GAf} {k N : ℕ}
    (hI : Integ L h) (hk : 0 < k) (hinv : ∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) (hu : L.CongOne (N * k) u) :
    L.CongOne N (h * u * h⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hinv v hv)
  refine ⟨L.actG h w, hI w hw, ?_⟩
  have hhv : L.actG h (L.actG h⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := conj_core (L.actG h).toAddMonoidHom (L.actG u).toAddMonoidHom (L.actG h⁻¹).toAddMonoidHom hk (v := v) (w := w) hhv e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pAdmOf :
    AdmOf := by
  intro p _ D G L h k N hI hk hinv u hu
  refine ⟨congOne_conj L hI hk hinv hu.1, ?_⟩
  have e : (h * u * h⁻¹)⁻¹ = h * u⁻¹ * h⁻¹ := by group
  rw [e]
  exact congOne_conj L hI hk hinv hu.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PDescMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pDescMap :
    GenSm → EtDesc → PtEq → PtOrbit → WitCart → DescMap := by
  intro hSm hEt hEq hOrb hCart p _ D G L R _ _ gb M N' N XM X' X h hI hA' hA1 c Φc π₁ Φ₁ hWc hFin hEtc hSurj hW1
  have hAd : AdmK L (↑M) (↑N) h := by
    intro v hv
    have h1 := hA1 v hv
    have h2 : v ∈ L.KN ↑N' := by simpa using h1
    exact hA' v h2
  haveI hred : IsReduced XM.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field R XM.X XM.s
      (hSm p D R gb M XM).1).1
  haveI hsep : IsSeparated X.s := (hSm p D R gb N X).2.1
  haveI := hFin
  haveI := hEtc
  haveI := hSurj
  have hsq : π₁ ≫ X.s = c ≫ X'.s := hW1.1.trans hWc.1.symm
  obtain ⟨hepi, π, hπ⟩ := hEt c X'.s X.s π₁ hsq (by
    intro Ω _ _ x y hxy
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, _⟩ := hOrb p D G L R gb M N' XM X' c Φc hWc Ω x y hxy
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    exact (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω (x ≫ XM.s) x y rfl hys ox oy mx my θ hθ).1)
  have hπs : π ≫ X.s = X'.s := by
    rw [← cancel_epi c, ← Category.assoc, hπ, hW1.1, hWc.1]
  have wsq : ∀ {NN NN' : ℕ} (Y' : GenModel gb NN') (Y : GenModel gb NN) (g : G.GAf) (ρ : Y'.X ⟶ Y.X)
      (Ψ : Y'.univ.A.left ⟶ Y.univ.A.left), Wit L g Y' Y ρ Ψ → Ψ ≫ Y.univ.A.hom = Y'.univ.A.hom ≫ ρ := by
    rintro _ _ Y' Y g ρ Ψ ⟨_, o, ψ, φ, _, rfl⟩
    rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w ψ]
  have hC : IsPullback Φc XM.univ.A.hom X'.univ.A.hom c :=
    hCart p D G L R gb (↑M) (↑N') XM X' 1 (one_mem _) c Φc hWc
  haveI : IsReduced XM.univ.A.left := by
    haveI := XM.univ.ab.smooth
    exact GlobalTheory.isReduced_of_smooth_of_isReduced XM.univ.A.hom
  haveI : IsSeparated X.univ.A.hom := by
    haveI := X.univ.ab.proper
    infer_instance
  haveI : IsFinite Φc := MorphismProperty.of_isPullback (P := @IsFinite) hC.flip hFin
  haveI : Etale Φc := MorphismProperty.of_isPullback (P := @Etale) hC.flip hEtc
  haveI : Surjective Φc := MorphismProperty.of_isPullback (P := @Surjective) hC.flip hSurj
  have hsq2 : Φ₁ ≫ X.univ.A.hom = Φc ≫ X'.univ.A.hom ≫ π := by
    rw [wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  obtain ⟨hepi2, Φ, hΦ⟩ := hEt Φc (X'.univ.A.hom ≫ π) X.univ.A.hom Φ₁ hsq2 (by
    intro Ω _ _ x y hxy
    have hab : (x ≫ XM.univ.A.hom) ≫ c = (y ≫ XM.univ.A.hom) ≫ c := by
      have e := congrArg (· ≫ X'.univ.A.hom) hxy
      simpa [hC.w] using e
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθeq⟩ :=
      hOrb p D G L R gb M N' XM X' c Φc hWc Ω _ _ hab
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    have key := (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω ((x ≫ XM.univ.A.hom) ≫ XM.s) _ _ rfl hys ox oy mx my θ hθ).2
    obtain ⟨x', hx1, hx2⟩ : ∃ x' : sp Ω ⟶ ox.A.left, x' ≫ mx.φ = x ∧ x' ≫ ox.A.hom = 𝟙 _ :=
      ⟨mx.cart.1.lift x (𝟙 _) (by simp), mx.cart.1.lift_fst _ _ _, mx.cart.1.lift_snd _ _ _⟩
    obtain ⟨y', hy1, hy2⟩ : ∃ y' : sp Ω ⟶ oy.A.left, y' ≫ my.φ = y ∧ y' ≫ oy.A.hom = 𝟙 _ :=
      ⟨my.cart.1.lift y (𝟙 _) (by simp), my.cart.1.lift_fst _ _ _, my.cart.1.lift_snd _ _ _⟩
    have hP := my.cart.1.paste_horiz hC
    have hxy' : x' ≫ θ.left = y' := by
      apply hP.hom_ext
      · rw [Category.assoc, hθeq, ← Category.assoc, hx1, hxy, ← Category.assoc, hy1]
      · rw [Category.assoc, Over.w θ, hx2, hy2]
    calc x ≫ Φ₁ = x' ≫ mx.φ ≫ Φ₁ := by rw [← Category.assoc, hx1]
      _ = x' ≫ θ.left ≫ my.φ ≫ Φ₁ := by rw [key]
      _ = y' ≫ my.φ ≫ Φ₁ := by rw [← Category.assoc x', hxy']
      _ = y ≫ Φ₁ := by rw [← Category.assoc, hy1])
  have hΦs : Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
    rw [← cancel_epi Φc, ← Category.assoc, hΦ, wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  exact ⟨π, Φ, hπ, hΦ, hπs, hΦs⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtDesc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pEtDesc :
    ExtPts → EtDesc := by
  intro hE W Z Y B _ c _ _ _ pZ pY _ f hf hpts
  haveI : Flat c := inferInstance
  haveI : EffectiveEpi c := inferInstance
  haveI : IsReduced (pullback c c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst c c)
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hE pY _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      refine hpts Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) ?_ |>.trans ?_ <;> simp [pullback.condition]
  refine ⟨inferInstance, EffectiveEpi.desc c f (fun {T} g₁ g₂ h => ?_), EffectiveEpi.fac _ _ _⟩
  have e₁ : pullback.lift g₁ g₂ h ≫ pullback.fst c c = g₁ := pullback.lift_fst _ _ _
  have e₂ : pullback.lift g₁ g₂ h ≫ pullback.snd c c = g₂ := pullback.lift_snd _ _ _
  calc g₁ ≫ f = pullback.lift g₁ g₂ h ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, e₁]
    _ = pullback.lift g₁ g₂ h ≫ pullback.snd c c ≫ f := by rw [key]
    _ = g₂ ≫ f := by rw [← Category.assoc, e₂]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKSNice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKSNice :
    KNBasic → PowSm → TwFEt → SigmaFEt → KSNice := by
  intro hKN hP hT hS p _ D G L hsc R _ _ gb k T N J g
  have hq := T.e_q N
  obtain ⟨hsm, -, hpr⟩ := hP p D R gb N (T.M N) k
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (T.X.q (T.lev N))
    rw [← hq]
    infer_instance
  · show IsProjOver (T.X.q (T.lev N))
    rw [← hq]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (hpr hsc.cpt)
  · intro j
    dsimp only [UpperTheory.Gal.Int.Geo.KS.tower]
    have hne : ((L.KN ↑N).subgroupOf (g j).K).index ≠ 0 := by
      have h0 := (hKN p D G L 1).2.2 N (by norm_num) (by have := N.2.1; omega)
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h0
      exact left_ne_zero_of_mul h0
    haveI : ((L.KN ↑N).subgroupOf (g j).K).FiniteIndex := ⟨hne⟩
    refine ⟨_, hS _ _ _ (hT T.X _ _ ⟨?_, ?_⟩)⟩
    · exact one_mem _
    · intro u hu
      rw [T.K_eq] at hu ⊢
      simpa using UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd hu
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMapOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMemOp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU

theorem UpperTheory.Gal.G3.pMemOp :
    KNBasic → PlInv.{u} → HopDeep.{u} → HopEx.{u} → TwMem.{u} → SumFn.{u} → MemOp.{u} := by
  intro hKN _ hHD hHE hTw hSum p _ D G L R _ _ gb k T N J g j F _ _ Θ hΘ f hf
  classical
  have hnorm : ∀ c ∈ L.KN 1, ∀ u ∈ L.KN (g j).M.1, c * u * c⁻¹ ∈ L.KN (g j).M.1 :=
    fun c hc => (hKN p D G L (g j).M.1).1 c hc
  have hfin : ∀ (M' : ℕ) (K' : Subgroup G.GAf), 0 < M' → K' ≤ L.KN 1 → Finite (K' ⧸ (L.KN M').subgroupOf K') := by
    intro M' K' hM' hK'
    have h1 : (L.KN M').relIndex (L.KN 1) ≠ 0 := (hKN p D G L 1).2.2 M' one_pos hM'
    have h2 : (L.KN M').relIndex K' ≠ 0 := fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right hK' h0)
    haveI : ((L.KN M').subgroupOf K').FiniteIndex := ⟨h2⟩
    infer_instance
  have hMpos : 0 < (g j).M.1 := by have := (g j).M.2.1; omega
  have hNpos : 0 < N.1 := by have := N.2.1; omega
  have hUV : L.KN (g j).M.1 ≤ L.KN N.1 := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hV1 : L.KN N.1 ≤ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _)
  haveI := hfin _ (g j).K hMpos (g j).le_one
  haveI := hfin _ (g j).K hNpos (g j).le_one
  haveI := hfin (g j).M.1 (L.KN N.1) hMpos hV1
  letI : Fintype ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) := Fintype.ofFinite _
  have hadm : ∀ c ∈ (g j).K, T.X.admitted (T.lev (g j).M) (T.lev N) ((g j).h * c) := fun c hc =>
    ⟨(T.Δ_eq _).2 ((g j).int.mul (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc))), fun u hu => by
      rw [T.K_eq] at hu ⊢
      exact (g j).adm c hc u hu⟩
  have hmem : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ y,
      (g j).h * (c * u) * y ∈ L.KN N.1 ↔ (g j).h * c * y ∈ L.KN N.1 := by
    intro c hc u hu y
    have e : (g j).h * (c * u) * y = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c * y) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left _ ((g j).adm c hc u hu)
  have hpl : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ x,
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c * u)) x = T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * c) x := by
    intro c hc u hu x
    have e : (g j).h * (c * u) = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c) := by group
    rw [e]
    exact T.X.pl_left Θ (hadm c hc) (by rw [T.K_eq]; exact (g j).adm c hc u hu) x
  have hS := hSum T.X Θ (T.lev (g j).M) (T.lev N) ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    (fun a => (g j).h * (a.out : G.GAf)) (fun a => hadm _ a.out.2) f (fun y => by rw [hf y, T.K_eq])
  have hinv : ∀ k ∈ T.X.K (T.lev N), ∀ y, f (k * y) = f y := by
    intro k₀ hk₀ y
    rw [T.K_eq] at hk₀
    have hk₀K : k₀ ∈ (g j).K := (g j).le hk₀
    let σ : ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) → ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) :=
      fun a => ((a.out * ⟨k₀, hk₀K⟩ : (g j).K) : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    have hσ : Function.Injective σ := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf] at h1
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((a.out)⁻¹ * b.out : (g j).K) : G.GAf) = k₀ *
          ((((a.out * ⟨k₀, hk₀K⟩ : (g j).K))⁻¹ * (b.out * ⟨k₀, hk₀K⟩) : (g j).K) : G.GAf) * k₀⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm k₀ (hV1 hk₀) _ h1
    have hσb : Function.Bijective σ := Finite.injective_iff_bijective.1 hσ
    have hcard : Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * (k₀ * y) ∈ L.KN N.1} =
        Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * y ∈ L.KN N.1} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hσb) fun a => ?_)
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) (a.out * ⟨k₀, hk₀K⟩)
      have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
      have e : (σ a).out = a.out * ⟨k₀, hk₀K⟩ * w := hw
      have e2 : (((Equiv.ofBijective σ hσb) a).out : G.GAf) = (a.out : G.GAf) * k₀ * ((w : (g j).K) : G.GAf) := by
        simp [e]
      rw [e2, hmem _ ((g j).K.mul_mem a.out.2 hk₀K) _ hwU y]
      simp only [_root_.mul_assoc]
    rw [hf, hf, hcard]
  have hIsFn := hS.2.1 hinv
  have hle : T.X.K (T.lev (g j).M) ≤ T.X.K (T.lev N) := by
    rw [T.K_eq, T.K_eq]; exact hUV
  refine ⟨hIsFn, fun tr htr => ?_⟩
  refine (hHE T.X Θ hΘ (T.lev N) f hIsFn).2 _ ((hHD T.X Θ hΘ (T.lev N) f hIsFn).2 _ (T.lev (g j).M) hle hS.1 fun x => ?_)
  rw [← hS.2.2 x]
  have hU' : ∀ y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1), ((y.out : L.KN N.1) : G.GAf) ∈ T.X.K (T.lev N) := by
    intro y; rw [T.K_eq]; exact y.out.2
  have hex : ∀ k ∈ T.X.K (T.lev N), ∃! y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1),
      k * ((y.out : L.KN N.1) : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M) := by
    intro k hk
    rw [T.K_eq] at hk
    simp only [T.K_eq]
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (L.KN N.1)) ⟨k, hk⟩
    have hwU : ((w : L.KN N.1) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
    refine ⟨((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)), ?_, fun y' hy' => ?_⟩
    · have e : k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ =
          k * ((w : L.KN N.1) : G.GAf)⁻¹ * k⁻¹ := by
        rw [hw]; push_cast; group
      show k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ ∈ _
      rw [e]
      exact hnorm k (hV1 hk) _ ((L.KN (g j).M.1).inv_mem hwU)
    · rw [← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((y'.out⁻¹ * ⟨k, hk⟩ : L.KN N.1) : G.GAf) =
          ((y'.out : L.KN N.1) : G.GAf)⁻¹ * (k * ((y'.out : L.KN N.1) : G.GAf)⁻¹) * ((y'.out : L.KN N.1) : G.GAf)⁻¹⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm _ (hV1 ((L.KN N.1).inv_mem y'.out.2)) _ hy'
  have hTw' := hTw T.X Θ (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (T.X.isAdmissibleIntegralBasisChange_one hle) le_rfl
    (fun k hk u hu => by
      rw [T.K_eq] at hk hu ⊢
      exact hnorm k (hV1 hk) u hu)
    ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1))
    (fun c => (g j).h * (c.out : G.GAf)) (fun c => hadm _ c.out.2)
    (fun y => ((y.out : L.KN N.1) : G.GAf)) hU' hex ((T.tower N g).comm j) tr htr x
  refine Eq.trans hTw' ?_
  refine (Fintype.sum_prod_type' (fun (c : (g j).K ⧸ (L.KN N.1).subgroupOf (g j).K)
    (y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) =>
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf)) x)).symm.trans ?_
  refine Fintype.sum_bijective _ (cos_bij (g j).K (L.KN N.1) (L.KN (g j).M.1) (g j).le hUV) _ _ fun q => ?_
  obtain ⟨c, y⟩ := q
  have hcy : (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf) ∈ (g j).K := (g j).K.mul_mem c.out.2 ((g j).le y.out.2)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) ⟨_, hcy⟩
  have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
  dsimp only
  rw [hw]
  push_cast
  rw [hpl _ hcy _ hwU x, _root_.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPowSm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma smooth_pow_hom {S : Scheme.{0}} (A : Over S) (hA : Smooth A.hom) (k : ℕ) :
    Smooth (GlobalTheory.KS.pow A k).hom := by
  have hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom := by
    intro X Y e h
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
    infer_instance
  have hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom := by
    intro Y Z hY hZ
    rw [← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  induction k with
  | zero =>
    exact hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso
      Over.mkIdTerminal) (by dsimp; infer_instance)
  | succ k ih =>
    exact hiso ((productIsProduct _).conePointUniqueUpToIso
      (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)

theorem UpperTheory.Gal.G3.pPowSm :
    GenSm → PowSm := by
  intro hG p _ D R _ _ gb N X k
  obtain ⟨hs, hsep, -, hproj⟩ := hG p D R gb N X
  haveI := hs
  haveI := hsep
  haveI : Smooth X.univ.A.hom := X.univ.ab.smooth
  haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k
  haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom :=
    GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k
  refine ⟨inferInstance, inferInstance, fun hD => ?_⟩
  exact GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample k
end

