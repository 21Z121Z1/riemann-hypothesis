import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0004
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.CoefZeroOfPer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
  simp at this
  rw [H.sqrt_neg_disc_sq, ← this]

theorem exists_emb (b : Bool) : ∃ τ : E →+* ℂ, τ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
  cases b
  · exact GlobalTheory.CM.LatData.exists_embedding H (by simp [H.sqrt_neg_disc_sq])
  · exact GlobalTheory.CM.LatData.exists_embedding H H.sqrt_neg_disc_sq

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

def eP (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : {k // ty k = τ} ≃ Fin p :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).1 h)

def eQ (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) : {k // ty k = τ} ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).2 h)

def blk (k : Fin g) : Fin p ⊕ Fin q :=
  if h : ty k (H.rt : E) = H.rt0 then .inl (eP hty (ty k) h ⟨k, rfl⟩) else .inr (eQ hty (ty k) h ⟨k, rfl⟩)

theorem blk_inl (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inl (eP hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

theorem blk_inr (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inr (eQ hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

def per : D.La →+ (Fin g → ℂ) where
  toFun y k := ty k ((c y (blk hty k) : 𝓞 E) : E) / n
  map_zero' := by funext k; simp
  map_add' y y' := by funext k; simp [add_div]

theorem per_apply (y : D.La) (k : Fin g) : per hty c n y k = ty k ((c y (blk hty k) : 𝓞 E) : E) / n := rfl

theorem per_smul (a : 𝓞 E) (y : D.La) (k : Fin g) : per hty c n (a • y) k = ty k (a : E) * per hty c n y k := by
  simp [per_apply, mul_div_assoc]

theorem per_inl (y : D.La) (a : Fin p) (hc : c y = Finsupp.single (.inl a) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ H.rt0) : per hty c n y k = 0 := by
  rw [per_apply, hc, blk_inr hty (ty k) hk k rfl]
  simp

theorem per_inr (y : D.La) (b : Fin q) (hc : c y = Finsupp.single (.inr b) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ -H.rt0) : per hty c n y k = 0 := by
  have h : ty k (H.rt : E) = H.rt0 := (rt_cases (ty k)).resolve_right hk
  rw [per_apply, hc, blk_inl hty (ty k) h k rfl]
  simp

theorem coef_zero_of_per (hn : 0 < n) (y : D.La) (h : per hty c n y = 0) : c y = 0 := by
  ext m
  cases m with
  | inl a =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) true
    simp only [if_true] at hτ
    let k := ((eP hty τ hτ).symm a).1
    have hk : ty k = τ := ((eP hty τ hτ).symm a).2
    have hb : blk hty k = .inl a := by
      rw [blk_inl hty τ hτ k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1
  | inr b =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) false
    simp only [Bool.false_eq_true, if_false] at hτ
    have hτ' : τ (H.rt : E) ≠ H.rt0 := by rw [hτ]; exact fun h => Host_rt0_ne_neg (H := H) h.symm
    let k := ((eQ hty τ hτ').symm b).1
    have hk : ty k = τ := ((eQ hty τ hτ').symm b).2
    have hb : blk hty k = .inr b := by
      rw [blk_inr hty τ hτ' k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1

end PositivityTheory.Xgf.DPer

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.LieNormSquareOfFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

open GlobalTheory.CompanionTheory.Ar.Fl.lie_norm_square_of_family

theorem lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  intro E _ _ _ H D R _ ω C T h L ψ σ κ r n a u hF hκ hr hu
  obtain ⟨hlin, -, -, hlam⟩ := hF
  obtain ⟨P', φ, v', uC, Hm, χ, w, ⟨hg', hpb, hLB⟩, hvo, hAH, hdw, hrr⟩ := hr
  have laws := abelianSchemeLaws_all.1
  obtain ⟨Q, ψQ, hQg, hQpb, hQLB⟩ := exists_isPolFibre laws.polBaseChange σ T.pol
  obtain ⟨rig0, hrig0⟩ := P'.rigid
  obtain ⟨u0, Hm0, χ0, -, hAH0, -, -, d20, hend0, -⟩ := thetaUnifAV_all P' rig0 hrig0
  obtain ⟨rigT, hrigT⟩ := Q.rigid
  obtain ⟨uT, HmT, χT, -, hAHT, -, -, d2T, -, -⟩ := thetaUnifAV_all Q rigT hrigT
  have := T.t.comm
  have := C.P.isAb.comm
  have hψm : ∀ b, IsMonHom (ψ b) := fun b => (hlin b).isMonHom
  choose f hfm hfc using fun b : L => @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hQpb (ψ b) (hψm b)
  choose e hem hec using fun c : OK H =>
    @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hpb (C.act.act c) (C.act.hom c)
  choose F hFl using fun b : L => @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ uT u0 (f b) (hfm b)
  choose G hGl using fun c : OK H => hend0 (e c) (hem c)
  obtain ⟨K, hK⟩ := @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ u0 uC (𝟙 P'.A) inferInstance
  have hv'T : IsTangent v' := IsVecOver.isTangent hpb hvo (C.basis.1 0)
  have hd0 : u0.IsDiff (K w) v' := by
    simpa using HodgeUniq.isDiff_comp u0 uC d20 (𝟙 P'.A) K hK hv'T hdw
  have hKH : ∀ z z', hermForm Hm0 (K z) (K z') = hermForm Hm z z' :=
    (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' P' P' uC uC u0 uC Hm0 Hm χ0 χ hAH0 hAH (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      K K LinearMap.id LinearMap.id hK hK (fun z => by simp) (fun z => by simp)).1 (fun _ _ _ _ _ _ _ => Iff.rfl)
  have hkey : ∀ b b' : L, ∀ z z', hermForm HmT (F b z) (F b' z') = hermForm Hm0 (G (h b b') z) z' := by
    intro b b' z z'
    have W0 := (PairingFibre.lamEq_weilEq_over_ring laws R C.P C.P T.pol C.P (ψ b) (ψ b') (C.act.act (h b b'))
      (𝟙 _) (hψm b) (hψm b') (C.act.hom _) inferInstance ℂ σ).1 (hlam b b')
    have W1 := (PairingFibre.weilEq_iff hpb hpb hQpb hpb T.t.PP.isLB C.P.isLB Q.isLB P'.isLB (LBIso.symm hQLB)
      (LBIso.symm hLB) (hfc b) (hfc b') (hec (h b b'))
      (show (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left by simp) (𝟙 (Sp ℂ))).2 (by rw [Category.id_comp]; exact W0)
    have := (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' Q P' u0 u0 uT u0 HmT Hm0 χT χ0 hAHT hAH0 (f b) (f b')
      (e (h b b')) (𝟙 _) (F b) (F b') (G (h b b')) LinearMap.id (hFl b) (hFl b') (hGl _) (fun z => by simp)).1 W1 z z'
    simpa using this
  have hg1 : P'.g = 1 := hg'.trans C.dim
  choose c hc using fun x : OK H => CurveAdjoint.exists_scalar hg1 (G x)
  have pa : ∀ (b : OK H) (p : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A),
      Geo.Tor.pushHom hpb _ (p ≫ e b) = Geo.Tor.pushHom hpb _ p ≫ C.act.act b := fun b p =>
    Over.OverMorphism.ext (by
      show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
      rw [Category.assoc, hec, Category.assoc])
  have inj : ∀ p q : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, Geo.Tor.pushHom hpb _ p = Geo.Tor.pushHom hpb _ q → p = q :=
    fun p q e' => SymBaseChange.pushPt_injective hpb e'
  have sc : ∀ (b : OK H) (s : ℂ) (Gs : (Fin P'.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z, Gs z = s • z) →
      (∀ z, u0.ex (G b z) = u0.ex (Gs z)) → c b = s := fun b s Gs hG hh => by
    have e' := congrFun ((hc b 1).symm.trans ((LinearMap.congr_fun (CurveAdjoint.linear_eq_of_ex u0 _ _ hh) 1).trans
      (hG 1))) ⟨0, by omega⟩
    simpa using e'
  let j : OK H →+* ℂ := RingHom.mk'
    { toFun := c
      map_one' := sc 1 1 LinearMap.id (fun z => by simp) fun z => inj _ _ (by
        rw [hGl, pa, C.act.one, Category.comp_id, LinearMap.id_apply])
      map_mul' := fun b b' => sc _ _ (G b' ∘ₗ G b) (fun z => by
        rw [LinearMap.comp_apply, hc, hc, smul_smul, mul_comm]) fun z => inj _ _ (by
          rw [LinearMap.comp_apply, hGl, hGl, hGl, pa, pa, pa, C.act.mul, Category.assoc]) }
    fun b b' => sc _ _ (G b + G b') (fun z => by
      rw [LinearMap.add_apply, hc, hc, ← add_smul]; rfl) fun z => inj _ _ (by
        rw [LinearMap.add_apply, u0.ex_add, map_mul, hGl, hGl, hGl, pa, pa, pa, C.act.add, Hom.mul_def, Hom.mul_def,
          ← Category.assoc, comp_lift])
  have hj : ∀ x, j x = c x := fun _ => rfl

  have heig : C.v ≫ C.act.act (wK H) = CMCurveTest.scaleVec ω C.v := by
    obtain ⟨u_, hu_, hprod⟩ := C.eig
    rw [hprod]
    apply Over.OverMorphism.ext
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
    exact hu_ 0
  have hover : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (v' ≫ e (wK H)) := by
    show (v' ≫ e _).left ≫ φ = _
    rw [Over.comp_left, Category.assoc, hec, ← Category.assoc, hvo, Over.comp_left, Category.assoc]
  have hsc : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (CMCurveTest.scaleVec (σ ω) v') := by
    rw [heig]; exact CMCurveTest.isVecOver_scaleVec hvo ω
  have hvv : v' ≫ e (wK H) = CMCurveTest.scaleVec (σ ω) v' :=
    (existsUnique_isVecOver hpb.1 (C.v ≫ C.act.act (wK H))).unique hover hsc
  have hGw : G (wK H) (K w) = σ ω • K w := by
    haveI := hem (wK H)
    have h1 := HodgeUniq.isDiff_comp u0 u0 d20 (e (wK H)) (G (wK H)) (hGl _) hv'T hd0
    have h2 := CMCurveTest.isDiff_scaleVec u0 hd0 (σ ω)
    rw [← hvv] at h2
    exact HodgeUnique.eq_of_isDiff u0 (isTangent_comp hv'T (e (wK H))) h1 h2
  have hjk : K w ≠ 0 → ∀ x, c x = κ x := by
    intro hne x
    have hw : c (wK H) = σ ω := by
      have e' : (c (wK H) - σ ω) • K w = 0 := by rw [sub_smul, ← hc, hGw, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right hne)
    obtain ⟨⟨m, k⟩, hx, -⟩ := existsUnique_coord H x
    rw [← hj, hx]
    simp only [map_add, map_mul, map_intCast]
    rw [hj, hw, hκ]
  refine ⟨Q, ψQ, fun k => v' ≫ f (a k), uT, HmT, χT, fun k => F (a k) (K w), hQpb, hQLB, hAHT,
    fun k => ⟨?_, ?_⟩, fun k k' => ?_⟩
  · rw [Over.comp_left, Category.assoc, hfc, ← Category.assoc, hvo, hu k, Category.assoc]
    rfl
  · haveI := hfm (a k)
    exact HodgeUniq.isDiff_comp uT u0 d2T (f (a k)) (F (a k)) (hFl _) hv'T hd0
  · simp only [Matrix.of_apply]
    rw [hkey, hc, hermForm_smul_left, hKH]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, hermForm Hm w w = t := ⟨_, hermForm_self_eq_re hAH.1 w⟩
    rw [ht] at hrr ⊢
    simp only [Complex.ofReal_re] at hrr
    by_cases hne : K w = 0
    · have h0 : (t : ℂ) = 0 := by rw [← ht, ← hKH, hne]; simp [hermForm]
      have h0' : t = 0 := by exact_mod_cast h0
      rw [hrr, h0']
      simp
    · rw [hjk hne, hrr]
      push_cast
      ring

end PositivityTheory.Xgf
end

