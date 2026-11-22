import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLe

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickeningStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian : ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  first | exact @GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | exact GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteBigCellToBaseProdAffineSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellQF

open GlobalTheory.FlagMod (initSpan initSpan_le_of_tri)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {m : ℕ}

theorem initSpan_eq_of_lower {v v' : Fin m → M} (L : Matrix (Fin m) (Fin m) R)
    (hL : ∀ i j, i < j → L i j = 0) (hd : ∀ i, IsUnit (L i i))
    (h : ∀ i, v' i = ∑ j, L i j • v j) (i : ℕ) : initSpan R v' i = initSpan R v i := by
  have ht : L.IsLowerTriangular := fun a b hab => hL a b hab
  have hdet : IsUnit L.det := by
    rw [Matrix.det_of_lowerTriangular L ht]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => hd a)
  haveI : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
  have hti : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular ht
  have hinv : ∀ a, v a = ∑ j, L⁻¹ a j • v' j := fun a => by
    simp only [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul L hdet, Matrix.one_apply]
    simp
  refine le_antisymm (initSpan_le_of_tri (B := L.transpose) (fun a b hab => hL b a hab) h i)
    (initSpan_le_of_tri (B := (L⁻¹).transpose) (fun a b hab => hti hab) hinv i)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def baseVec (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) {K : Type} [CommRing K] (x : Sp K ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) : TanM x TF.Y.t.G :=
  LieMet.tanOf (v := spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev x U.1 hU) (hv (e ⟨σ, j⟩))
    unfold LogKS.chart at this
    rwa [GlobalTheory.FlagMod.spMap_ev x U.2 hU] at this)

theorem vecAt_eq_sum (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i =
      ∑ j, ev z W hz ((L σ * N σ) i j) • baseVec TF U e v hv x hU σ j := by
  subst ex
  have hc := h.2.2.2.2.2.2.2 K z hz hU hk hx σ i
  exact (LieMet.isComb_iff (fun j => baseVec TF U e v hv _ hU σ j)
    (fun j => ev z W hz ((L σ * N σ) i j)) _).1 hc

theorem step_eq_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) (σ : E →+* ℂ) (i : ℕ) :
    TF.X.F.step (z ≫ inc₀ TF.X Z) hx σ i =
      initSpan K (fun a => ∑ j, ev z W hz (N σ a j) • baseVec TF U e v hv x hU σ j) i := by
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 hz
  rw [TF.X.F.step_eq k _ hk hx]
  refine initSpan_eq_of_lower (fun a b => ev z W hz (L σ a b))
    (fun a b hab => by rw [h.2.2.2.1 σ a b hab, map_zero]) (fun a => (h.2.2.2.2.1 σ a).map _) (fun a => ?_) i
  rw [vecAt_eq_sum TF Z U e v hv W k L N h z hz ex hU hk hx σ a]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end GlobalTheory.LogPole.CellQF

namespace GlobalTheory.LogPole.CellQF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem locallyOfFiniteType_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_comp_C]
  exact h1

end GlobalTheory.LogPole.CellQF

set_option maxHeartbeats 1000000 in
open GlobalTheory.LogPole.CellQF in

theorem GlobalTheory.LogPole.locallyQuasiFinite_cellMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N h
  haveI := locallyOfFiniteType_cell TF Z U e v W k L N h
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_points _ fun Ω _ _ y => ?_
  have hfs : IsOpenImmersion h.1.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec h.1
  have hzW : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W), ⊤ ≤ (x ≫ h.1.fromSpec) ⁻¹ᵁ W :=
    fun x => GlobalTheory.FlagMod.le_preimage_comp x (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have hsp : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      spMap (ev (x ≫ h.1.fromSpec) W (hzW x)) = x := fun x => by
    rw [← cancel_mono h.1.fromSpec]
    exact GlobalTheory.FlagMod.spMap_ev _ h.1 _
  have hy : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      spMap ((ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y := fun x => by
    rw [← spMap_comp', hsp]
    exact x.2
  have hρ : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) =
      (ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) := fun x x' =>
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((hy x).trans (hy x').symm))
  have hN : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}, ∀ σ a b,
      ev (x.1 ≫ h.1.fromSpec) W (hzW x.1) (N σ a b) = ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1) (N σ a b) := by
    intro x x' σ a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · have e1 : N σ a b = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)
          (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩) := by
        rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [e1]
      exact congrArg (fun f => f (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩)) (hρ x x')
    · rw [h.2.2.2.2.2.2.1 σ a, map_one, map_one]
    · rw [h.2.2.2.2.2.1 σ a b hab]
      exact (RingHom.map_zero _).trans (RingHom.map_zero _).symm
  have hUx : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ⊤ ≤ ((x ≫ h.1.fromSpec) ≫ toBase TF Z) ⁻¹ᵁ U.1 :=
    fun x => GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzW x)
  have hev : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ev ((x ≫ h.1.fromSpec) ≫ toBase TF Z) U.1 (hUx x) = ((ev (x ≫ h.1.fromSpec) W (hzW x)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))).comp MvPolynomial.C :=
    fun x => by
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE _ _ h.2.1 (hzW x)]
    simp
  have hB : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = (x'.1 ≫ h.1.fromSpec) ≫ toBase TF Z := fun x x' => by
    refine (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x.1)).symm.trans (Eq.trans ?_ (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x'.1)))
    rw [hev x.1, hev x'.1, hρ x x']
  rcases isEmpty_or_nonempty {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}
    with h0 | hne
  · exact @Finite.of_subsingleton _ ⟨fun a => (h0.false a).elim⟩
  obtain ⟨x₀⟩ := hne
  have ex₀ : (x₀.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
    (Category.assoc _ _ _).symm
  have hU0 : ⊤ ≤ (((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π) ⁻¹ᵁ U.1 := by
    rw [← ex₀]; exact hUx x₀.1
  have hfin := TF.flag.fin Ω ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z)
  have key : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      ∃ hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π,
      ∀ (σ : E →+* ℂ) (i : ℕ), TF.X.F.step ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) hx σ i =
        TF.X.F.step ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) rfl σ i := fun x => by
    have ex : (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (hB x x₀).trans ex₀
    have hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (Category.assoc _ _ _).trans ex
    refine ⟨hx, fun σ i => ?_⟩
    refine (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x.1) ex hU0 hx σ i).trans ?_
    refine Eq.trans ?_ (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x₀.1) ex₀ hU0 rfl σ i).symm
    simp only [hN x x₀]
  have hinj : Function.Injective
      (fun x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) => (x ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) :=
    fun a b hab => (cancel_mono h.1.fromSpec).1 ((cancel_mono (inc₀ TF.X Z)).1 hab)
  have hS : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) | x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}.Finite :=
    (hfin.preimage hinj.injOn).subset fun x hx => key ⟨x, hx⟩
  exact hS.to_subtype
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOrdFracComapFormallyUnramifiedDvr
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrictOrd

open IsLocalRing

theorem isLocalHom_restrict {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) :
    IsLocalHom (φ.restrict (V.comap φ) V fun _ hx => hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha
  have hb' : ((b : V) : L) = φ (a : K) := by
    rw [hb]; rfl
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((b : V) : L) = 0 := by rw [hb', h0, map_zero]
    exact b.ne_zero (Subtype.ext this)
  have hmem : (a : K)⁻¹ ∈ V.comap φ := by
    change φ (a : K)⁻¹ ∈ V
    rw [map_inv₀, ← hb']
    have : ((b⁻¹ : Vˣ) : V) * (b : V) = 1 := b.inv_mul
    have h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
    rw [← h2]
    exact ((b⁻¹ : Vˣ) : V).2
  exact isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem log_ordFrac_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)] :
    (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra;
      Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) →
    ∀ g : K, g ≠ 0 →
      WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  intro h g hg
  set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef
  letI := ψ.toAlgebra
  obtain ⟨hu, he⟩ := h
  haveI : IsLocalHom ψ := isLocalHom_restrict φ V
  haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)
  have hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have ht' : Irreducible (ψ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg

end GlobalTheory.RestrictOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogShortThetaSeriesDenominatorBoundLeStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_shortThetaSeriesDenominatorBound_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n →
    0 < intZ D (T.Q.Dw j) Y.d.l₂ n a ∧
    Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n := by
  first | exact @GlobalTheory.CovIntNum.intZ_log_le | exact GlobalTheory.CovIntNum.intZ_log_le | (intros; apply GlobalTheory.CovIntNum.intZ_log_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicDerivationLocalizationAtPrimeSpanOfRi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem logDerivation_atPrime_span : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (I : Ideal A) (n : ℕ) (b : Fin n → Derivation ℤ A A), (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∀ D' : Derivation F R R, (∀ f ∈ I.map (algebraMap A R), D' f ∈ I.map (algebraMap A R)) → ∃ c : Fin n → R, ∀ a : A, D' (algebraMap A R a) = ∑ j, c j * algebraMap A R (b j a) := by
  intro F A R _ _ _ _ _ _ _ _ _ P _ _ I n b hb D' hD'
  classical

  have hloc : IsLocalizedModule P.primeCompl (Algebra.linearMap A R) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have : Module.FinitePresentation A Ω[A⁄F] := Module.finitePresentation_of_finite _ _
  let Dc : Derivation F A R := D'.compAlgebraMap A
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    P.primeCompl (Algebra.linearMap A R) Dc.liftKaehlerDifferential
  let D₀ : Derivation F A A := h.compDer (KaehlerDifferential.D F A)
  have hD₀ : ∀ y : A, algebraMap A R (D₀ y) = algebraMap A R (s : A) * D' (algebraMap A R y) := by
    intro y
    have := congrArg (fun φ => φ (KaehlerDifferential.D F A y)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    simpa [D₀, Dc] using this

  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ g ∈ G, ∃ t ∈ P.primeCompl, t * D₀ g ∈ I := by
    intro g hg
    have hgI : g ∈ I := hG ▸ Ideal.subset_span hg
    have : algebraMap A R (D₀ g) ∈ I.map (algebraMap A R) := by
      rw [hD₀]
      exact Ideal.mul_mem_left _ _ (hD' _ (Ideal.mem_map_of_mem _ hgI))
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R I _).mp this
  choose! tg htgP htgI using hgen
  let t' : A := ∏ g ∈ G, tg g
  have ht'P : t' ∈ P.primeCompl := by
    have := prod_mem (S := P.primeCompl) (t := G) (f := tg) (fun g hg => htgP g hg)
    simpa [t'] using this
  let D₁ : Derivation ℤ A A := t' • (D₀.restrictScalars ℤ)
  have hD₁ : ∀ x, D₁ x = t' * D₀ x := fun x => by simp [D₁, smul_eq_mul]
  have hkill : ∀ c, D₁ (algebraMap F A c) = 0 := fun c => by
    rw [hD₁, Derivation.map_algebraMap, mul_zero]
  have hkeep : ∀ f ∈ I, D₁ f ∈ I := by
    intro f hf
    rw [← hG] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [hD₁]
      have hd : tg x ∣ t' := Finset.dvd_prod_of_mem _ hx
      obtain ⟨k, hk⟩ := hd
      rw [hk, mul_comm (tg x) k, mul_assoc]
      exact Ideal.mul_mem_left _ _ (htgI x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul a x hxs hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ ?_)
      rw [hG] at hxs; exact hxs
  obtain ⟨c, hc⟩ := hb D₁ hkill hkeep

  have hu : IsUnit (algebraMap A R (t' * s)) :=
    IsLocalization.map_units R (⟨t' * s, P.primeCompl.mul_mem ht'P s.2⟩ : P.primeCompl)
  refine ⟨fun j => hu.unit⁻¹ * algebraMap A R (c j), fun a => ?_⟩
  have e1 : algebraMap A R (D₁ a) = ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [hc]
    have : ∀ (s : Finset (Fin n)), (∑ j ∈ s, c j • b j) a = ∑ j ∈ s, c j * b j a := by
      intro s; induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Derivation.add_apply, ih, Derivation.smul_apply, smul_eq_mul]
    rw [this, map_sum]; simp only [map_mul]
  have e2 : algebraMap A R (D₁ a) = algebraMap A R (t' * s) * D' (algebraMap A R a) := by
    rw [hD₁, map_mul, hD₀, map_mul, mul_assoc]
  rw [e2] at e1
  have : D' (algebraMap A R a) = (hu.unit⁻¹ : Rˣ) * ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [← e1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this, Finset.mul_sum]
  simp only [mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

def GenOn {Y : Scheme.{0}} (L : LB Y) (O : Y.Opens) (s : ∀ k, Γ(Y, L.U k ⊓ O)ˣ) : Prop :=
  ∀ (k l : L.ι) (y : Y), y ∈ L.U k → y ∈ L.U l → y ∈ O →
    gm (𝟙 Y) y (L.U k ⊓ O) (s k) = gm (𝟙 Y) y (L.U k ⊓ L.U l) (L.g k l) * gm (𝟙 Y) y (L.U l ⊓ O) (s l)

def Matched {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (LZ : LB Z)
    (w : LB.Iso (L'.pull i') (LZ.pull p')) (O' : X'.Opens) (OZ : Z.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ O')ˣ)
    (sZ : ∀ j, Γ(Z, LZ.U j ⊓ OZ)ˣ) : Prop :=
  ∀ (z : Z') (j : LZ.ι) (k : L'.ι), p' z ∈ LZ.U j → i' z ∈ L'.U k → p' z ∈ OZ → i' z ∈ O' →
    gm p' z (LZ.U j ⊓ OZ) (sZ j) =
      gm (𝟙 Z') z ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) *
        gm i' z (L'.U k ⊓ O') (s' k)

end GlobalTheory.PinchLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataRestrictionUnique
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKRealConj

theorem realMaps_transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (R₂ : RealMaps F a a'),
    IsTriple B (reG G V V' W) X om om' → IsRealMaps B (reG G V V' W) om om' R₂ →
    ∀ g ∈ UAt σ G.V (evI F), ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F),
    (∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w))) →
    (∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w))) →
    (∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
    ∃ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ ∧ ∀ (Rf : FinMaps F a a') Φ Φ', PolMatch B G X R₃ Rf Φ Φ' →
        PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') :=
  GlobalTheory.T.real_maps_relevant_space

theorem soLoc_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.SoLoc ψ t = G.M'.SoLoc ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩

theorem so_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t := by
  unfold Model.So
  rw [soLoc_reG']
  rfl

end GlobalTheory.ThKRealConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndexStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_det_im_pos_at_index : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  first | exact @GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | exact GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | (intros; apply GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_detOneFactor_nearIdentity_le : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → m {u | ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε} ≤ ENNReal.ofReal ((200 * ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * ε ^ ((p + q) ^ 2 - 1)) := by
  first | exact @GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le | exact GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le | (intros; apply GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le <;> assumption)
end

