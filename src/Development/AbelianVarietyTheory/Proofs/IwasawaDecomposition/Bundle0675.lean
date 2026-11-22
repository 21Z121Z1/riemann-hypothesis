import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

def dualHom {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) : A →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_mul' f f' := by ext <;> simp [hm, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f f' := by ext <;> simp

@[simp] theorem dualHom_fst {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).fst = e f := by
  simp [dualHom]

@[simp] theorem dualHom_snd {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).snd = D f := by
  simp [dualHom]

theorem derivation_eq_zero_of_etale {k A : Type} [CommRing k] [CommRing A] {g : ℕ}
    (φ : MvPolynomial (Fin g) k →+* A) (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ)
    (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have hP : ∀ q, D (φ q) = 0 := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add q r hq hr => rw [map_add, map_add, hq, hr, add_zero]
    | mul_X q i hq => rw [map_mul, hm, hq, hX]; simp
  let F : A →+* DualNumber ℂ := dualHom e D hm
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ q, F (φ q) = F₀ (φ q) := fun q => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) k) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) k) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F₀ with commutes' := fun q => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.PointDer

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_eq_fderiv : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  intro k _ Y p n σ c x₀ hx₀ U hU δ hδ0 hδm
  have hxc : x₀ ∈ ptsIn p σ c.U := c.source_subset hx₀
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 c.affine _
    ⟨mem_ptsIn.1 hU, mem_ptsIn.1 hxc⟩
  have hWc : Y.basicOpen g ≤ c.U := Y.basicOpen_le g
  have hWU : Y.basicOpen g ≤ U.1 := hfg ▸ Y.basicOpen_le f
  have hxW : x₀ ∈ ptsIn p σ (Y.basicOpen g) := mem_ptsIn.2 (hfg ▸ hxf)

  have hmU : ∀ a b, δ (a * b) = evHom hU a * δ b + evHom hU b * δ a := fun a b => by
    rw [hδm, ev_eq hU, ev_eq hU]
  let ψU := dualHom (evHom hU) δ hmU
  letI : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen g) := (resG Y hWU).toAlgebra
  haveI : IsLocalization.Away f Γ(Y, Y.basicOpen g) :=
    U.2.isLocalization_of_eq_basicOpen f (homOfLE hWU) hfg.symm
  have hfu : IsUnit (ψU f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst, isUnit_iff_ne_zero, ← ev_eq hU]
    exact (mem_ptsIn_basicOpen hU f).1 (mem_ptsIn.2 hxf)
  let ψW : Γ(Y, Y.basicOpen g) →+* DualNumber ℂ := IsLocalization.Away.lift f hfu
  have hψW (a : Γ(Y, U.1)) : ψW (resG Y hWU a) = ψU a := IsLocalization.Away.lift_eq f hfu a
  have hψW1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ψW = evHom hxW := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    change (ψW (resG Y hWU a)).fst = evHom hxW (resG Y hWU a)
    rw [hψW, dualHom_fst, ← ev_eq, ← ev_eq, ev_res _ hxW]
  have hfst (a : Γ(Y, Y.basicOpen g)) : (ψW a).fst = evHom hxW a := RingHom.congr_fun hψW1 a

  let v : ReciprocityTheory.L2DbarEstimates.V n := WithLp.toLp 2 (fun b => (ψW (resG Y hWc (c.x b))).snd)

  have hdW := fun a : Γ(Y, Y.basicOpen g) => c.differentiableAt_ev a hx₀ hxW
  let dW : Γ(Y, Y.basicOpen g) → ℂ := fun a => fderiv ℂ (ev p σ _ a ∘ c.e.symm) (c.e x₀) v
  have hdadd (a b) : dW (a + b) = dW a + dW b := by
    have e : ev p σ _ (a + b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) + (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_add _ _ _
    simp only [dW, e, fderiv_add (hdW a) (hdW b), ContinuousLinearMap.add_apply]
  have hdmul (a b) : dW (a * b) = evHom hxW a * dW b + evHom hxW b * dW a := by
    have e : ev p σ _ (a * b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) * (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_mul _ _ _
    simp only [dW, e, fderiv_mul (hdW a) (hdW b), Function.comp_apply, c.e.left_inv hx₀,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← ev_eq hxW]
  have hn : ∀ᶠ w in 𝓝 (c.e x₀), c.e.symm w ∈ ptsIn p σ (Y.basicOpen g) :=
    Filter.eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds
      (ChartGlue.mem_over c.e hx₀ hxW)) fun _ h => h.2

  let Dd : Γ(Y, Y.basicOpen g) →+ ℂ := AddMonoidHom.mk' (fun a => (ψW a).snd - dW a) fun a b => by
    simp only [map_add, TrivSqZeroExt.snd_add, hdadd]
    ring
  have hD : Dd = 0 := by
    refine derivation_eq_zero_of_etale ((resG Y hWc).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x))
      ?_ (evHom hxW) Dd ?_ ?_ ?_
    · have hR : (resG Y hWc).Etale := by
        letI : Algebra Γ(Y, c.U) Γ(Y, Y.basicOpen g) := (resG Y hWc).toAlgebra
        haveI : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
          c.affine.isLocalization_of_eq_basicOpen g (homOfLE hWc) rfl
        exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway g)
      exact RingHom.Etale.stableUnderComposition _ _ c.etale hR
    · intro a
      have e1 : (resG Y hWc) (MvPolynomial.eval₂Hom (algX p c.U) c.x (MvPolynomial.C a)) =
          resG Y hWU (algX p U.1 a) := by
        rw [MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX,
          ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
      have e2 : dW (resG Y hWU (algX p U.1 a)) = 0 := by
        have e : ev p σ _ (resG Y hWU (algX p U.1 a)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] fun _ => σ a := by
          filter_upwards [hn] with w hw
          rw [Function.comp_apply, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
          exact ev_algX hw a
        show fderiv ℂ _ _ v = 0
        rw [e.fderiv_eq]
        simp
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, e1, hψW, ψU, dualHom_snd, hδ0, e2, sub_zero]
    · intro a b
      simp only [Dd, AddMonoidHom.mk'_apply, map_mul, TrivSqZeroExt.snd_mul, hfst, hdmul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    · intro i
      have e2 : dW (resG Y hWc (c.x i)) = v i := by
        have e : ev p σ _ (resG Y hWc (c.x i)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)]
            EuclideanSpace.proj (𝕜 := ℂ) i := by
          filter_upwards [hn, c.e.open_target.mem_nhds (c.e.map_source hx₀)] with w hw hwt
          rw [Function.comp_apply, ev_res hWc hw, ← c.apply_eq _ (c.e.map_target hwt) i,
            c.e.right_inv hwt]
          rfl
        simp only [dW, e.fderiv_eq, ContinuousLinearMap.fderiv]
        rfl
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', e2]
      simp [v]
  refine ⟨v, fun a => ?_⟩
  have h1 := congrArg (fun D : Γ(Y, Y.basicOpen g) →+ ℂ => D (resG Y hWU a)) hD
  simp only [Dd, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply, hψW, dualHom_snd, sub_eq_zero] at h1
  rw [show δ a = (ψU a).snd from (dualHom_snd _ _ _ a).symm, h1]
  have e : ev p σ _ (resG Y hWU a) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] ev p σ U.1 a ∘ c.e.symm := by
    filter_upwards [hn] with w hw
    exact ev_res hWU hw a
  simp only [dW, e.fderiv_eq]

end GlobalTheory.PointDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem isLB_of_chartPull {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X)) (hc : ⨆ i, A.U i = ⊤) :
    A.IsLB where
  cover := hc
  g_self i := by
    apply unit_ext
    intro x hx
    rw [gm_res (𝟙 X) x _ hx, map_one, a.g x i i hx hx]
    exact gm_self hB (𝟙 X) x (a.le i hx)
  cocycle i j k := by
    apply unit_ext
    intro x hx
    have hi : x ∈ A.U i := hx.1.1
    have hj : x ∈ A.U j := hx.1.2
    have hk : x ∈ A.U k := hx.2
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      a.g x i j hi hj, a.g x j k hj hk, a.g x i k hi hk]
    exact gm_cocycle hB (𝟙 X) x (a.le i hi) (a.le j hj) (a.le k hk)

theorem nsmul_trans (D : EffCartierData X) (n : ℕ) (i j : D.ι) :
    (D.nsmul n).trans i j = D.trans i j ^ n := by
  symm
  apply (D.nsmul n).eq_trans i j
  show resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i ^ n) =
    ((D.trans i j ^ n : Γ(X, D.U i ⊓ D.U j)ˣ) : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j ^ n)
  rw [map_pow, map_pow, D.trans_spec i j, mul_pow, Units.val_pow_eq_pow_val]

theorem gm_lbPow (L : LB X) (k : ℕ) (y : X) (j j' : PUnit → L.ι) (hj : (𝟙 X) y ∈ (lbPow L k).U j)
    (hj' : (𝟙 X) y ∈ (lbPow L k).U j') :
    gm (𝟙 X) y ((lbPow L k).U j ⊓ (lbPow L k).U j') ((lbPow L k).g j j') =
      gm (𝟙 X) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)) ^ k := by
  dsimp only [lbPow, LB.LinComb]
  have hy : (𝟙 X) y ∈ L.wchart (fun _ => 𝟙 X) j ⊓ L.wchart (fun _ => 𝟙 X) j' := ⟨hj, hj'⟩
  have hy' : (𝟙 X) ((𝟙 X) y) ∈ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    ⟨Set.mem_iInter.1 hj PUnit.unit, Set.mem_iInter.1 hj' PUnit.unit⟩
  simp only [Fintype.prod_unique, zpow_natCast]
  refine (map_pow (gm (𝟙 X) y _) _ k).trans ?_
  congr 1
  refine (gm_res (𝟙 X) y _ hy _).trans ((gm_pull (𝟙 X) (𝟙 X) y _ hy' _).trans ?_)
  rw [Category.comp_id]

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

theorem evalZ_comb_mul {O : Type} [CommRing O] (ψ φ : InvFun O) (x y n : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (be : LinearMap.BilinForm ℤ M) :
    (comb (n * x) ψ (n * y) φ).evalZ be = n * (comb x ψ y φ).evalZ be := by
  simp only [InvFun.evalZ, InvFun.eval, comb]
  push_cast
  ring

def scaleChart (Dm : LB X) (D : EffCartierData X) (m n : ℕ) :
    ChartPull (CechPic.tens (lbPow Dm (n * m)) (CechPic.dual (D.nsmul n).lb))
      (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n) (𝟙 X) where
  idx p := fun _ => p
  le _ _ hy := Set.mem_iInter.2 fun _ => hy
  g y p q hp hq := by
    have hp' : (𝟙 X) y ∈ (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n).U (fun _ => p) :=
      Set.mem_iInter.2 fun _ => hp
    have hq' : (𝟙 X) y ∈ (lbPow (CechPic.tens (lbPow Dm m) (CechPic.dual D.lb)) n).U (fun _ => q) :=
      Set.mem_iInter.2 fun _ => hq
    rw [gm_lbPow _ n y _ _ hp' hq', CechPic.gm_tens _ _ (𝟙 X) y p q hp hq,
      CechPic.gm_tens (lbPow Dm m) (CechPic.dual D.lb) (𝟙 X) y p q hp hq,
      gm_lbPow Dm (n * m) y _ _ hp.1 hq.1, gm_lbPow Dm m y _ _ hp.1 hq.1]
    have e₁ : gm (𝟙 X) y _ ((CechPic.dual (D.nsmul n).lb).g p.2 q.2) = (gm (𝟙 X) y _ (D.trans p.2 q.2) ^ n)⁻¹ := by
      refine (map_inv (gm (𝟙 X) y _) _).trans (congrArg (·⁻¹) ?_)
      refine (congrArg (gm (𝟙 X) y _) (nsmul_trans D n p.2 q.2)).trans ?_
      exact map_pow _ _ _
    have e₂ : gm (𝟙 X) y _ ((CechPic.dual D.lb).g p.2 q.2) = (gm (𝟙 X) y _ (D.trans p.2 q.2))⁻¹ :=
      map_inv (gm (𝟙 X) y _) _
    rw [e₁, e₂, mul_pow, inv_pow, ← pow_mul, mul_comm n m]

theorem scale_pol {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (ψ φ : InvFun (𝓞 E)) (x y m n : ℕ) (BD : EffCartierData Z.X) : 0 < n → IsPol (comb x ψ y φ) m Z BD →
    ∃ BD' : EffCartierData Z.X, IsPol (comb (n * x) ψ (n * y) φ) (n * m) Z BD' := by
  intro hn h
  refine ⟨BD.nsmul n, ?_, ?_⟩
  · intro W _ _ _ hW ϖ hϖ χ t s P hr be hbe hmono
    obtain ⟨k, hk, hI⟩ := h.1 W hW ϖ hϖ χ t s P hr be hbe hmono
    refine ⟨k * n, ?_, ?_⟩
    · rw [evalZ_comb_mul, ← hk]
      push_cast
      ring
    · rw [idlAlong_nsmul, hI, Ideal.span_singleton_pow, pow_mul]
  · have hA : GlobalTheory.IsAmpleLB (polOf Z m BD) := h.2
    have hpow : GlobalTheory.IsAmpleLB (lbPow (polOf Z m BD) n) := (isAmpleLB_basic.2.1 hA.isLB hn).2 hA
    have hc : ⨆ p, (polOf Z (n * m) (BD.nsmul n)).U p = ⊤ := by
      apply top_unique
      intro z _
      have hz : z ∈ (⊤ : Z.X.Opens) := trivial
      rw [← hpow.isLB.cover, TopologicalSpace.Opens.mem_iSup] at hz
      obtain ⟨J, hJ⟩ := hz
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨J PUnit.unit, Set.mem_iInter.1 hJ PUnit.unit⟩
    have hQ : (polOf Z (n * m) (BD.nsmul n)).IsLB :=
      isLB_of_chartPull hpow.isLB (scaleChart (GlobalTheory.FlagMod.detOm Z) BD m n) hc
    exact (isAmpleLB_congr hQ hpow.isLB
      (CechPic.iso_of_chart hpow.isLB (scaleChart (GlobalTheory.FlagMod.detOm Z) BD m n))).2 hpow

end GlobalTheory.TorRef.Scale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem dvd_of_traits {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    {a b : R} (ha : a ≠ 0)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      g a ∣ g b) : a ∣ b := by
  refine GlobalTheory.dvd_of_forall_height_eq_one ha fun p _ hp _ => ?_
  let V := Localization.AtPrime p
  have hV : IsDiscreteValuationRing V := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp V
  have hi : Function.Injective (algebraMap R V) := IsLocalization.injective V p.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨i1, i2⟩, i3, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR V
  let g := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hg : Function.Injective (g.comp (algebraMap R V)) := hinj.comp hi
  have hd : g (algebraMap R V a) ∣ g (algebraMap R V b) :=
    h _ ⟨i2, i3, charZero_of_injective_ringHom hg⟩ _ hg
  have hd' : algebraMap R V a ∣ algebraMap R V b := by
    rcases ValuationRing.dvd_total (algebraMap R V a) (algebraMap R V b) with h1 | ⟨e, he⟩
    · exact h1
    · obtain ⟨d, hd⟩ := hd
      have h0 : g (algebraMap R V a) ≠ 0 := fun e0 => ha (hg (e0.trans (map_zero _).symm))
      have h1 : g e * d = 1 := by
        apply mul_left_cancel₀ h0
        have := congrArg g he
        rw [map_mul, hd] at this
        rw [mul_one]
        linear_combination -this
      obtain ⟨u, rfl⟩ : IsUnit e := isUnit_of_map_unit g e (IsUnit.of_mul_eq_one _ h1)
      exact ⟨(u⁻¹ : Vˣ), by rw [he, Units.mul_inv_cancel_right]⟩
  obtain ⟨z, hz⟩ := hd'
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj p.primeCompl z
  refine ⟨s, s.2, r, hi ?_⟩
  rw [map_mul, map_mul, hz, ← hrs]
  ring

theorem span_eq_of_traits {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    {a b : R} (ha : a ≠ 0)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      (Ideal.span {a}).map g = (Ideal.span {b}).map g) : Ideal.span {a} = Ideal.span {b} := by
  have h' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      Associated (g a) (g b) := fun W _ _ _ hW g hg => by
    have := h W hW g hg
    rwa [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Ideal.span_singleton_eq_span_singleton] at this
  have hb : b ≠ 0 := by
    rintro rfl
    let K := FractionRing R
    have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
    have hg : Function.Injective ((PowerSeries.C (R := K)).comp (algebraMap R K)) :=
      PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    have := h' _ (GlobalTheory.FrameCmp.cDvr_powerSeries K) _ hg
    rw [map_zero, associated_zero_iff_eq_zero] at this
    exact ha (hg (this.trans (map_zero _).symm))
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd
    (dvd_of_traits ha fun W _ _ _ hW g hg => (h' W hW g hg).dvd)
    (dvd_of_traits hb fun W _ _ _ hW g hg => (h' W hW g hg).symm.dvd))

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) {K : Type} [Field K]
    (g : Z.X.presheaf.stalk x →+* K) (hg : Function.Injective g) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = Spec.map (CommRingCat.ofHom g) ≫ Z.X.fromSpecStalk x := by
  obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
  have := (Z.normal x).1
  refine GlobalTheory.HomExt.exists_lift_of_range_subset Z.j _ ?_
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, hξ, hs⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
  have hξ' := GlobalTheory.genericPoints_subset_range_of_isDominant Z.j hξ
  obtain ⟨q, rfl⟩ : ξ ∈ Set.range (Z.X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  have ht : Spec.map (CommRingCat.ofHom g) t ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap g t.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime, Ideal.comap_bot_of_injective _ hg]
    exact bot_le
  have h2 := ht.map (Z.X.fromSpecStalk x).continuous
  have h3 := (hξ : Maximal IsIrreducible _).2 isIrreducible_singleton.closure (specializes_iff_closure_subset.1 h2)
  rw [Scheme.Hom.comp_apply, (h2.antisymm (specializes_iff_closure_subset.2 h3)).eq]
  exact hξ'

theorem idealSheaf_eq_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (_ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' → ∀ π : Z'.X ⟶ Z.X, Z'.j ≫ π = r ≫ Z.j →
    BD'.idealSheaf = BD.idealSheaf.comap π := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ σ r ν hβ hβ' _ htw hσ hB hB' π hπ
  obtain ⟨h₁, -⟩ := GlobalTheory.ModelRelCompare.densePart Z' hβ'
  refine GlobalTheory.Vanishing.eq_comap_of_stalk fun x => ?_
  obtain ⟨hd, hn⟩ := Z'.normal x
  obtain ⟨i, hi⟩ := BD.exists_mem (π x)
  obtain ⟨i', hi'⟩ := BD'.exists_mem x
  have hz : CharZero (Z'.X.presheaf.stalk x) := by
    obtain ⟨y, -⟩ := exists_lift Z' hβ' x _ (IsFractionRing.injective _ (FractionRing (Z'.X.presheaf.stalk x)))
    have := charZero_of_point (K := .of (FractionRing (Z'.X.presheaf.stalk x))) y
    exact ⟨fun p q e => Nat.cast_injective (R := FractionRing (Z'.X.presheaf.stalk x)) (by
      simpa using congrArg (algebraMap _ (FractionRing (Z'.X.presheaf.stalk x))) e)⟩
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W →
      ∀ g : Z'.X.presheaf.stalk x →+* W, Function.Injective g → (FinalTheorems.stalkId BD'.idealSheaf x).map g =
        ((FinalTheorems.stalkId BD.idealSheaf (π x)).map (π.stalkMap x).hom).map g := by
    intro W _ _ _ hW g hg
    obtain ⟨y, hy⟩ := exists_lift Z' hβ' x ((algebraMap W (FractionRing W)).comp g)
      ((IsFractionRing.injective W _).comp hg)
    have e1 : jK W ≫ Spec.map (CommRingCat.ofHom g) ≫ Z'.X.fromSpecStalk x = y ≫ Z'.j := by
      rw [hy, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have e2 : Spec.map (CommRingCat.ofHom (g.comp (π.stalkMap x).hom)) ≫ Z.X.fromSpecStalk (π x) =
        (Spec.map (CommRingCat.ofHom g) ≫ Z'.X.fromSpecStalk x) ≫ π := by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    rw [Ideal.map_map, ← idlAlong_fromSpecStalk, ← idlAlong_fromSpecStalk]
    refine GlobalTheory.T.polarization_transfer_models E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' φ σ r ν hβ hβ' htw hσ hB hB' W hW _ _ y e1 ?_
    rw [e2, ← Category.assoc, e1, Category.assoc, hπ]
  rw [BD.stalkId_idealSheaf i _ hi, BD'.stalkId_idealSheaf i' _ hi', Ideal.map_span, Set.image_singleton] at key ⊢
  exact span_eq_of_traits (nonZeroDivisors.ne_zero (Cartier.isRegularFn_iff_germ.1 (BD'.regular i') x hi')) key

end GlobalTheory.PolDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullWIsConj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam

namespace GlobalTheory.AmpleKaehler

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def pullW (Z : TrueGeo.Model Y) (L : HermLB Z.p) (σ : F →+* ℂ) : Weight Y.str σ (L.B.pull Z.j) :=
  (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => OfModel.ptMap Z σ) fun _ _ => rfl

variable (Z : TrueGeo.Model Y) (L : HermLB Z.p)

theorem pullW_φ (σ : F →+* ℂ) (i : (L.B.pull Z.j).ι) (y : Pts Y σ) :
    (pullW Z L σ).φ i y = (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ (i PUnit.unit) (OfModel.ptMap Z σ y) :=
  (Fintype.sum_unique fun a : PUnit.{1} =>
    ((1 : ℤ) : ℝ) * (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ (i a) (OfModel.ptMap Z σ y)).trans (by simp)

theorem pullW_isConj (σ σ' : F →+* ℂ) : (pullW Z L σ').IsConj (pullW Z L σ) := by
  intro i y y' hy hi
  rw [pullW_φ, pullW_φ]
  refine L.conj (σ'.comp (algebraMap (𝓞 F) F)) (σ.comp (algebraMap (𝓞 F) F)) (i PUnit.unit)
    (OfModel.ptMap Z σ' y) (OfModel.ptMap Z σ y') ?_
    (mem_of_mem_linComb (m := fun _ => OfModel.ptMap Z σ' y) (fun _ => rfl) hi PUnit.unit)
  change y'.1 ≫ Z.j = spMap (starRingEnd ℂ) ≫ y.1 ≫ Z.j
  rw [hy, Category.assoc]

end GlobalTheory.AmpleKaehler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannFormFramePointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_frame_point : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec <;> assumption)
end

