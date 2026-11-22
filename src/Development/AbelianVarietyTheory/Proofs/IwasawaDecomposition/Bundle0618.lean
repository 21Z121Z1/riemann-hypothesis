import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConst
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dif_pos h]
  rfl

theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlatSec

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_trans {R k : Type} [CommRing R] [Field k] {φ : c.F →+* R} {φ' φ'' : c.F →+* k} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp k ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* k} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (h : f.Tri ψ g t) (h' : g.Tri (RingHom.id k) g' d) :
    f.Tri ψ g' (fun τ i => t τ i * d τ i) := by
  have h1 : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨e1, e2, h'⟩ := h'
  rw [h1, Category.id_comp] at e1
  subst e1
  refine ⟨rfl, e2, fun τ i => ?_⟩
  choose a a1 a2 a3 using h τ
  obtain ⟨cf, b1, b2, b3⟩ := h' τ i
  simp only [h3, Category.id_comp] at b3
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k := fun j i => a i j
  have hA : A.BlockTriangular id := fun j k hk => a2 k j hk
  obtain ⟨c1, c2⟩ := Guard.tri_mulVec hA b2
  refine ⟨A.mulVec cf, ?_, c1, tanLinG _ (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)) _ A cf _ a3 b3⟩
  rw [c2, b1, show A i i = t τ i from a1 i, Units.val_mul]

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

variable {K : Type} [Field K] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ)

end Gen

end GlobalTheory.ShFam.FlatSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorFrHolo

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)

theorem isDerivAt0_of_cart {g : ℕ} {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) (pt : Sp ℂ ⟶ X') {e : (Fin g → ℂ) → (Sp ℂ ⟶ G')} (he : ∀ z, e z ≫ h' = pt)
    (hol : IsHolTo Set.univ fun z => e z ≫ φ) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'}
    (hv : v ≫ h' = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ pt) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  have H := (IsPullback.of_hasPullback h' pt).paste_horiz hc
  have key := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp]))
    (fun z => pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hol)
    (v := pullback.lift v _ hv) (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using isDerivAt0_comp_hom key (pullback.fst h' pt)

theorem isHolTo_lift {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) {n g : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (a : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (ha : IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => a bz.1 bz.2) (hp : IsHolTo B p)
    (w : ∀ b z, a b z ≫ h = p b ≫ f) :
    IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => hc.lift (a bz.1 bz.2) (p bz.1) (w _ _) := by
  let L : (Fin (n + g) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin g → ℂ) :=
    ((LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin g) ℂ ℂ)).toContinuousLinearEquiv
  have hC : IsOpen (L ⁻¹' (B ×ˢ Set.univ)) := (hB.prod isOpen_univ).preimage L.continuous
  have h1 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => a (L c).1 (L c).2 :=
    LocLift.isHolTo_comp ha hC L.differentiableOn fun _ h => h
  have h2 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => p (L c).1 :=
    LocLift.isHolTo_comp hp hC (β := fun c => (L c).1) (by fun_prop) fun _ h => h.1
  have h3 := holPair _ _ _ h f _ _ _ _ (fun c => w (L c).1 (L c).2) hC h1 h2
  have h4 := isHolTo_comp h3 hc.isoPullback.inv
  have key : ∀ c, pullback.lift (a (L c).1 (L c).2) (p (L c).1) (w _ _) ≫ hc.isoPullback.inv =
      hc.lift _ _ (w (L c).1 (L c).2) := fun c => hc.hom_ext
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.lift_fst]
      exact pullback.lift_fst _ _ _)
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.lift_snd]
      exact pullback.lift_snd _ _ _)
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h4 ((hB.prod isOpen_univ)) (β := L.symm)
    L.symm.differentiableOn fun q hq => by simpa using hq) fun q _ => ?_
  refine Eq.trans ?_ (key (L.symm q)).symm
  simp only [L.apply_symm_apply]

section Family

open GlobalTheory.TrueCx.TorHolo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

theorem exists_family (hU : IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    ∃ (g : ℕ) (q : Fin g ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))
      (Ft : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ft bz.1 bz.2) ∧
      ∀ b ∈ B, ∀ cf : Fin g → ℂ, IsDerivAt0 (Ft b) cf (tv (∑ i, cf i • torBasis Y (U.un k (x b)) (q i))).left := by
  classical
  obtain ⟨-, -, -, -, -, g, q, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hxu hder _ using hun k
  have h1 := F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩
  have hc := Y.m0.toSABMap.cart.1
  have hw : ∀ b z, (F.ex (ik k) (P (x b)) z).left ≫ Xo.univ.t.G.hom =
      ptC (U.un k (x b)) ≫ pullback.fst _ _ := fun b z => by
    rw [ptC_fst, xC, hxu]
    exact Over.w (F.ex (ik k) (P (x b)) z)
  have hp : IsHolTo B fun b => ptC (U.un k (x b)) := by
    refine isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_
    simp only [ptC_fst]
    exact LocLift.isHolTo_congr h1.1 fun b _ => hxu _
  have h2 := isHolTo_lift hc hB (fun b z => (F.ex (ik k) (P (x b)) z).left) _ h1.2 hp hw
  refine ⟨g, q, fun b z => hc.lift _ _ (hw b z) ≫ Y.m.φ, isHolTo_comp h2 _, fun b hb cf => ?_⟩
  set y := U.un k (x b) with hy
  have hne : IsHolTo Set.univ fun z => (F.ex (ik k) (P (x b)) z).left :=
    LocLift.isHolTo_comp h1.2 isOpen_univ (β := fun z => (b, z)) (by fun_prop) fun _ _ => ⟨hb, trivial⟩
  have hT : ∀ (u : TanM (xC y) Xo.univ.t.G) (w : Fin g → ℂ),
      IsDerivAt0 (fun z => (F.ex (ik k) (P (x b)) z).left) w (tv u).left →
      IsDerivAt0 (fun z => hc.lift _ _ (hw b z) ≫ Y.m.φ) w (tv (lieEquiv Y y u)).left := fun u w h => by
    set u' := (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm u with hu'
    have h3 : (tv u').left ≫ Y.m0.toSABMap.φ = (tv u).left := by
      rw [← left_pushE Y.m0.toSABMap (ptC y) (ptC_fst y), hu', LinearEquiv.apply_symm_apply]
    have h4 := isDerivAt0_of_cart hc (ptC y) (e := fun z => hc.lift _ _ (hw b z))
      (fun z => hc.lift_snd _ _ _) (by simpa only [IsPullback.lift_fst] using hne)
      (isTan_tv u').1 (by simpa only [IsPullback.lift_fst, h3] using h)
    exact isDerivAt0_comp_hom h4 Y.m.φ
  have hsum : ∑ i, cf i • torBasis Y y (q i) = lieEquiv Y y (∑ i, cf i • frVec y (q i)) := by
    simp only [map_sum, map_smul, torBasis, Module.Basis.map_apply, Module.Basis.mk_apply]
  rw [hsum]
  refine hT _ _ ?_
  have e0 : (F.ex (ik k) (P (x b)) 0).left = (1 : Over.mk (xC y) ⟶ Xo.univ.t.G).left := by
    have key : ∀ {a b' : Sp ℂ ⟶ Xo.X} (_ : a = b'), (1 : Over.mk a ⟶ Xo.univ.t.G).left =
        (1 : Over.mk b' ⟶ Xo.univ.t.G).left := by
      rintro _ _ rfl
      rfl
    rw [(F.ex_ker _ _ (hP' _) 0).2 (zero_mem _)]
    exact key (hxu _).symm
  have h5 := ShFam.Hor.ExpDirs.isDerivAt0_of_comb (t := Xo.univ.t) (x := xC y) e0
    (v := fun i => (tv (frVec y (q i))).left) (w := fun i => Pi.single i 1) (fun i => isTan_tv _)
    (fun i => by
      have h := hder (x b) (q i).1 (q i).2
      rw [Sigma.eta, Equiv.symm_apply_apply] at h
      exact h) (a := cf) (isTan_tv _) ((isComb_iff (fun i => frVec y (q i)) cf _).2 rfl)
  have h6 : ∑ i, cf i • (Pi.single i 1 : Fin g → ℂ) = cf := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [h6] at h5

end Family

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ) (r j : ℕ) (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (Tau : Type) [Fintype Tau] (T : Tau ≃ Psi H) (k : U.Comp) (V : (torC Y σ).affineOpens) (v : TanM (LogKS.chart V ≫ torPr Y σ) Y.t.G) (i : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ∃ g : Pt Tau j (r - j) → ℂ, ∀ z ∈ DomI Tau j (r - j), ∀ hy : domTor Y U hU e T k z ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1, DifferentiableAt ℂ (fun w => g (unflat w)) (flat z) ∧ g z = (torBasis Y (domFr U hU e T k z)).repr (valAt (torPr Y σ) v hy) i := by
  intro E _ _ _ H Dw l Xo c Y σ r j U hU e hσ Tau _ T k V v i
  classical
  let L : (Tau × Fin j × Fin (r - j) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat Tau j (r - j)) := ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) := L.symm ⁻¹' DomFlat Tau j (r - j) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) (first_index_eq_of_unfolded U hU e k) (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B := fun τ a c =>
    ((TorHolo.differentiable_stdMat (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  obtain ⟨g, q, Ft, hFt, hD⟩ := exists_family Y hU k hB x hd
  have hY : IsHolTo B fun b => (domTor Y U hU e T k (unflat (L.symm b))).1 := TorHolo.isHolTo_torPt Y hU k hB x hd
  let Wz : Pt Tau j (r - j) → Fin g → ℂ := fun z =>
    if h : domTor Y U hU e T k z ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 then
      fun m => (torBasis Y (domFr U hU e T k z)).repr (valAt (torPr Y σ) v h) (q m) else 0
  set W : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → Fin g → ℂ := fun b => Wz (unflat (L.symm b)) with hWdef
  set B' := {b ∈ B | ⊤ ≤ (domTor Y U hU e T k (unflat (L.symm b))).1 ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  have hsum : ∀ b (hb : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1),
      ∑ m, W b m • torBasis Y (U.un k (x b)) (q m) = valAt (torPr Y σ) v hb := fun b hb => by
    have h1 : W b = fun m => (torBasis Y (domFr U hU e T k (unflat (L.symm b)))).repr (valAt (torPr Y σ) v hb) (q m) :=
      dif_pos hb
    rw [h1]
    exact (q.sum_comp fun a => (torBasis Y (domFr U hU e T k (unflat (L.symm b)))).repr (valAt (torPr Y σ) v hb) a •
      torBasis Y (domFr U hU e T k (unflat (L.symm b))) a).trans ((torBasis Y _).sum_repr _)
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : domTor Y U hU e T k (unflat (L.symm b₀)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 := hb₀.2
    let ev : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → (Γ(torC Y σ, V.1) →+* ℂ) := fun b =>
      if h : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 then evHom h else evHom h₀
    have hevb : ∀ b (h : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1),
        ev b = evHom h := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom hb.2).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (Ft b) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ (tv v).left) := fun b hb => by
      have h1 := hD b hb.1 (W b)
      rw [hsum b hb.2, hevb b hb.2] at *
      exact h1
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, O)), ⊤ ≤ Ft b₀ 0 ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (Ft b₀ z) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (Ft b z) O f) 0)
        (HolLieFrame.differentiableAt_fderiv (e := Ft) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd (tv v).left ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (Ft b₀) w hw'
    have d₀ := LocalLift.isDerivAt0_const (Ft b₀) 0 fun _ _ _ => map_zero _
    have e3 := tan_ext ((isDerivAt0_unique (hD b₀ hb₀.1 w) d₁).trans (isDerivAt0_unique (hD b₀ hb₀.1 0) d₀).symm)
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e3
    exact funext (Fintype.linearIndependent_iff.1 ((torBasis Y (U.un k (x b₀))).linearIndependent.comp q q.injective) w e3)
  refine ⟨fun z => Wz z (q.symm i), fun z hz hy => ⟨?_, ?_⟩⟩
  · have e1 : L.symm (L (flat z)) = flat z := L.symm_apply_apply _
    have hb : L (flat z) ∈ B' := by
      refine ⟨?_, ?_⟩
      · show L.symm (L (flat z)) ∈ DomFlat Tau j (r - j)
        rw [e1]
        exact hz
      · rw [e1]
        exact hy
    have h1 := (differentiableAt_pi.1 (hdiff _ hb) (q.symm i)).comp (flat z) L.differentiableAt
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp [hWdef]
  · show (dite _ _ _ : Fin g → ℂ) (q.symm i) = _
    rw [dif_pos hy]
    simp

end GlobalTheory.TrueCx.TorFrHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingOfMinimal
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.SpecialStalk

theorem natCast_eq_zero_of_not_charZero {V k : Type} [CommRing V] [IsLocalRing V] [Field k] (φ : V →+* k) {p : ℕ}
    (hp : p.Prime) (hV : (p : V) ∈ maximalIdeal V) (hk : ¬ CharZero k) : (p : k) = 0 := by
  obtain ⟨l, hl⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k l with h | rfl
  · by_cases e : l = p
    · exact e ▸ CharP.cast_eq_zero k l
    · exfalso
      have hc : IsCoprime (l : V) (p : V) := Nat.Coprime.cast ((Nat.coprime_primes h hp).2 e)
      have hu : IsUnit (l : V) := by
        by_contra hn
        obtain ⟨a, b, hab⟩ := hc
        exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem
          (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hn)) (Ideal.mul_mem_left _ _ hV)))
      have := (hu.map φ).ne_zero
      rw [map_natCast] at this
      exact this (CharP.cast_eq_zero k l)
  · exact absurd (CharP.charP_to_charZero k) hk

theorem isDiscreteValuationRing_of_minimal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) (hm : a ∈ maximalIdeal R)
    (h : ∀ P : Ideal R, P.IsPrime → a ∈ P → P = maximalIdeal R) : IsDiscreteValuationRing R := by
  have hne : maximalIdeal R ≠ ⊥ := fun e => ha (by simpa [e] using hm)
  have hf : ¬ IsField R := fun hf => hne (isField_iff_maximalIdeal_eq.1 hf)
  have hmin : maximalIdeal R ∈ (Ideal.span {a}).minimalPrimes :=
    ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 hm⟩, fun P hP _ =>
      (h P hP.1 ((Ideal.span_singleton_le_iff_mem _).1 hP.2)).ge⟩
  have hle : (maximalIdeal R).height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have key := (IsDiscreteValuationRing.TFAE R hf).out 3 0
  refine key.1 ⟨inferInstance, maximalIdeal R, ⟨hne, inferInstance⟩, fun P hP => ?_⟩
  have := hP.2
  by_contra hn
  have h1 := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne (le_maximalIdeal hP.2.ne_top) hn)
  exact hP.1 (Ideal.height_eq_zero_iff_eq_bot.1 (Order.lt_one_iff.1 (h1.trans_le hle)))

theorem mem_of_dense {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → y = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e ▸ hξ.specializes (hs hyo)).mem_open hU hyU

theorem countable_stalk {V : Type} [CommRing V] [Countable V] {X : Scheme.{0}} (f : X ⟶ Sp V) [LocallyOfFiniteType f]
    (x : X) : Countable (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h1 : Countable Γ(Sp V, ⊤) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1.countable
  have h2 : (f.appLE ⊤ U le_top).hom.FiniteType := f.finiteType_appLE (isAffineOpen_top _) hU _
  have h3 : Countable Γ(X, U) := by
    obtain ⟨n, g, hg⟩ := (@Algebra.FiniteType.iff_quotient_mvPolynomial'' _ _ _ _ (f.appLE ⊤ U le_top).hom.toAlgebra).1 h2
    have : Countable (MvPolynomial (Fin n) Γ(Sp V, ⊤)) := AddMonoidAlgebra.coeff_injective.countable
    exact hg.countable
  let _ := X.presheaf.algebra_section_stalk (U := U) ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact (IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl).countable

noncomputable def toStalk {V : Type} [CommRing V] {X : Scheme.{0}} (f : X ⟶ Sp V) (x : X) : V →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp
    (((Sp V).presheaf.germ ⊤ (f x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)

theorem charZero_stalk {V : Type} [CommRing V] [IsDomain V] [CharZero V] {X : Scheme.{0}} (f : X ⟶ Sp V) [Flat f]
    (x : X) : CharZero (X.presheaf.stalk x) := by
  have fl : (toStalk f x).Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)) ?_) (Flat.stalkMap f x)
    have hU := isAffineOpen_top (Sp V)
    let _ := (Sp V).presheaf.algebra_section_stalk (U := ⊤) ⟨f x, trivial⟩
    have := hU.isLocalization_stalk ⟨f x, trivial⟩
    exact IsLocalization.flat ((Sp V).presheaf.stalk ((⟨f x, trivial⟩ : (⊤ : (Sp V).Opens)) : Sp V))
      (hU.primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl
  let _ := (toStalk f x).toAlgebra
  have : Module.Flat V (X.presheaf.stalk x) := fl
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V _)

theorem not_charZero_fromSpecStalk {X : Scheme.{0}} (x : X) (q : Spec (X.presheaf.stalk x)) {p : ℕ} (hp : p ≠ 0)
    (h : (p : X.presheaf.stalk x) ∈ q.asIdeal) : ¬ CharZero (X.residueField (X.fromSpecStalk x q)) := by
  intro hc
  have := charZero_of_injective_ringHom (f := (Scheme.Spec.residueFieldIso (X.presheaf.stalk x) q).hom.hom.comp
    ((X.fromSpecStalk x).residueFieldMap q).hom) (RingHom.injective _)
  have := q.isPrime
  have h1 := Ideal.algebraMap_residueField_eq_zero.2 h
  rw [map_natCast] at h1
  exact hp (by exact_mod_cast h1)

theorem stalkSt : GlobalTheory.LocM.Cht.StalkSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z η
  have := Z.i.c.fin
  have : NumberField Z.i.c.F := {}
  have hW' : (p : Z.i.c.F) ∈ (Z.i.c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp.ne_zero hW').1
  have hV : (p : Z.i.c.V W) ∈ maximalIdeal (Z.i.c.V W) := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hW'
  have : Countable Z.i.c.F := Countable.of_equiv _ (Module.finBasis ℚ Z.i.c.F).equivFun.toEquiv.symm
  have : IsProper (PSpace.str (Z.i.c.V W) Z.n) := isProper_str _ _
  have : IsProper Z.s := inferInstanceAs (IsProper (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n))
  have := Z.flat
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have : IsNoetherian Z.X := {}
  have hdom := Z.normal.isDomain_stalk η.1
  have := Z.normal.isIntegrallyClosed_stalk η.1
  have hcz := charZero_stalk Z.s η.1
  have hm : (p : Z.X.presheaf.stalk η.1) ∈ maximalIdeal (Z.X.presheaf.stalk η.1) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact natCast_eq_zero_of_not_charZero ((residue _).comp (toStalk Z.s η.1)) hp hV η.2.1
  have hsp : ∀ q : Spec (Z.X.presheaf.stalk η.1), Z.X.fromSpecStalk η.1 q ⤳ η.1 := fun q => by
    have : Z.X.fromSpecStalk η.1 q ∈ Set.range (Z.X.fromSpecStalk η.1) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hdom, isDiscreteValuationRing_of_minimal (Nat.cast_ne_zero.2 hp.ne_zero) hm fun P hP h => ?_, hcz,
    countable_stalk Z.s η.1, hm, fun q hq => mem_of_dense (fun y hy => ?_) ?_ Z.dense⟩
  · have e := η.2.2 _ (not_charZero_fromSpecStalk η.1 (⟨P, hP⟩ : PrimeSpectrum _) hp.ne_zero h) (hsp _)
    exact congrArg PrimeSpectrum.asIdeal ((Z.X.fromSpecStalk η.1).isEmbedding.injective
      (e.trans Scheme.fromSpecStalk_closedPoint.symm))
  · obtain ⟨q', rfl⟩ : y ∈ Set.range (Z.X.fromSpecStalk η.1) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy.trans (hsp q)
    have h := (PrimeSpectrum.le_iff_specializes q' q).2
      ((Z.X.fromSpecStalk η.1).isEmbedding.isInducing.specializes_iff.1 hy)
    exact congrArg _ (le_antisymm (α := PrimeSpectrum _) h (show q.asIdeal ≤ q'.asIdeal from hq ▸ bot_le))
  · rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2

end GlobalTheory.SpecialStalk
end

