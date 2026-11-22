import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0715
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0724
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarrySpec

theorem carries_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk :=
  GlobalTheory.CarrySpec.spec_of_anypoint GlobalTheory.T.carried_frame_triangular_through_stalkFrames

end GlobalTheory.CarrySpec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwistChoice

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev thTw (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) : TwNew D :=
  ⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, th, D.ntwbr, D.ntwbr_ind⟩

theorem carried_thTw (D0 D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) (h : Carried D0 D) :
    Carried D0 (thTw D th).toD7 :=
  ⟨⟨{ h.exp.gal with }, { h.exp.set with }, { h.exp.frm with }, h.exp.br, h.exp.av⟩, h.emb⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_exists_marked_form_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  first | exact @GlobalTheory.PolFan.carries_exists_marked | exact GlobalTheory.PolFan.carries_exists_marked | (intros; apply GlobalTheory.PolFan.carries_exists_marked <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonalStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

def avgC {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra ℂ G :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ h : G, MonoidAlgebra.of ℂ G (h * g * h⁻¹)

theorem center_eq_sum {G : Type} [Group G] [Fintype G] (z : MonoidAlgebra ℂ G)
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : z = ∑ g : G, z.coeff g • avgC g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ = z := by
    intro h
    rw [hz, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h2 : z = ∑ g : G, z.coeff g • MonoidAlgebra.of ℂ G g := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc z = (Fintype.card G : ℂ)⁻¹ • ∑ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ := by
        simp only [h1, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = ∑ g : G, z.coeff g • avgC g := by
        conv_lhs => rw [h2]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, avgC, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        rw [← map_mul, ← map_mul, smul_comm]

theorem avgC_mem {G : Type} [Group G] [Fintype G] (g : G) : avgC g ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgC, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

def avgK (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra K G :=
  ((Fintype.card G : K)⁻¹) • ∑ h : G, MonoidAlgebra.of K G (h * g * h⁻¹)

theorem avgK_coeff {K : Type} [Field K] {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (e : G ≃* H)
    (g y : G) : σ ((avgK K g).coeff y) = (avgC (e g)).coeff (e y) := by
  simp only [avgK, avgC, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, map_mul, map_inv₀,
    map_natCast, map_sum, apply_ite, map_one, map_zero]
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_inv]
  classical
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hy : h * g * h⁻¹ = y
  · rw [if_pos hy, if_pos (congrArg e hy), map_one]
  · rw [if_neg hy, if_neg (fun h' => hy (e.injective h')), map_zero]

theorem lin_center {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    (Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₗ[ℂ] W) (v : G → W)
    (h : ∀ g₁, Φ ⟨avgC g₁, avgC_mem g₁⟩ = ∑ g₀, (avgC g₁).coeff g₀ • v g₀)
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    Φ z = ∑ g₀, (z : MonoidAlgebra ℂ G).coeff g₀ • v g₀ := by
  have hz : z = ∑ g₁, (z : MonoidAlgebra ℂ G).coeff g₁ •
      (⟨avgC g₁, avgC_mem g₁⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [SetLike.val_smul]
    exact center_eq_sum _ z.2
  conv_lhs => rw [hz]
  rw [map_sum]
  simp only [map_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [center_eq_sum _ z.2]
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.coe_finset_sum, Finset.sum_apply]

theorem avgK_comm (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) (b : MonoidAlgebra K G) :
    b * avgK K g = avgK K g * b := by
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgK, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem avgK_conj (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g c y : G) :
    (avgK K g).coeff (c * y * c⁻¹) = (avgK K g).coeff y := by
  classical
  simp only [avgK, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun h => ?_).symm
  rw [Finsupp.single_apply, Finsupp.single_apply]
  refine if_congr ⟨fun e => ?_, fun e => ?_⟩ rfl rfl
  · rw [← e]; simp [mul_assoc]
  · have e' : c * (h * g * h⁻¹) * c⁻¹ = c * y * c⁻¹ := by rw [← e]; simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel e')

theorem actSum_apply (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : Formalism.AUTREP.GAf D.host.E n → W) (g : Formalism.AUTREP.GAf D.host.E n) :
    GlobalTheory.PendOf.actSum D L z f g = ∑ g₀ : G0g D.nd, z.coeff g₀ • f (g * L g₀) := by
  unfold GlobalTheory.PendOf.actSum
  rw [Finsupp.sum_fintype _ _ (by intros; simp)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

section Rows

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)

def ratForm (k : Fin D.R.m) (s : T) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) :=
  D.what₂.jMt (Y.tup s) ((k : ℕ) + 1) (Y.eMt k s x)

variable (F) in

def lvlAct (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL :=
  ((A3.A.fam.L k s).S.lvlOp (A3.A.fam.L k s).r (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).P (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).ψ a).mulVec x

def adForm (μ : D.what₂.Tup) (h : Used0 D μ) (k : Fin D.R.m) :
    D.what₂.Mt μ ((k : ℕ) + 1) →ₗ[ℂ] (GA D (Vc D k) → (R.cV k).W) where
  toFun x := (Y.IL.jMt μ h k x).1
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

def CenRat : Prop :=
  ∀ (s : T) (k : Fin D.R.m) (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) →
    ∀ x, D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z (ratForm Y k s x) = ratForm Y k s (lvlAct F k s a x)

def ActRead : Prop :=
  ∀ (s : T) (h : Used0 D (Y.tup s)) (k : Fin D.R.m) (a : MonoidAlgebra D.what₂.LL G), (∀ b, b * a = a * b) →
    ∀ κ : G → GA D (Vc D k), (∀ g, Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (κ g)) →
    ∀ x y, adForm Y (Y.tup s) h k (ratForm Y k s (lvlAct F k s a x)) y =
      ∑ g : G, (D.what₂.embLL (a.coeff g) * (Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (κ g))⁻¹) •
        adForm Y (Y.tup s) h k (ratForm Y k s x) (y * κ g)

def FrameAt (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV) (s : T) : Prop :=
  ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
    (Nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) → ∃ c : G, ∀ g : G,
      Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
      Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1)

set_option maxHeartbeats 1000000 in

theorem cenLoc_of (M : MtFam D) (ad : MtAd Y M) (h1 : CenRat Y cG) (h2 : ActRead Y)
    (h3 : ∀ (i : D.nd.Loc) (s : T) (k : Fin D.R.m), Y.tup s = D.nd.mu i → FrameAt Y cG k (ad.PV k) s) : CenLoc D M := by
  intro i
  suffices H : ∀ μ, Used0 D μ → ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m),
      (∀ (s : T) (k : Fin D.R.m), Y.tup s = μ → FrameAt Y cG k (ad.PV k) s) →
      ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
        ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
          (M μ j hj1 hj2).real (D.ntypes.cenMt μ j z x) =
            GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j hj1 hj2).real x) from
    H _ (Model.used_loc i) _ (D.nd.j_range i).1 (D.nd.j_range i).2 (h3 i)
  intro μ hμ j hj1 hj2 h3
  obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, Y.tup s = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨L, hL, hc⟩ := h3 s k rfl
  refine ⟨L, hL, fun z x => funext fun g => ?_⟩
  rw [actSum_apply]
  rcases subsingleton_or_nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) with h0 | h0
  · rw [Subsingleton.elim x 0]; simp
  obtain ⟨c, hc⟩ := hc h0
  have key : ∀ g₁ : G0g D.nd,
      adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ x) ((ad.PV k).ψ g) =
        ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀)) := by
    intro g₁
    have tie : ∀ y, D.what₂.embLL ((avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff y) = (avgC g₁).coeff ((R.eG.trans cG) y) :=
      fun y => by rw [avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      (LinearMap.proj ((ad.PV k).ψ g)).comp ((adForm Y (Y.tup s) hμ k).comp
        (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩))
    let F2 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      { toFun := fun y => ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k y ((ad.PV k).ψ (g * L g₀))
        map_add' := fun y y' => by simp only [map_add, Pi.add_apply, smul_add, Finset.sum_add_distrib]
        map_smul' := fun c y => by
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _ }
    have hb := (D.what₂.jMt_basis (Y.tup s) ((k : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt k s).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)) b)
      rw [← hx']
      show adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ (ratForm Y k s x'))
        ((ad.PV k).ψ g) = ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k (ratForm Y k s x') ((ad.PV k).ψ (g * L g₀))
      rw [h1 s k ⟨avgC g₁, avgC_mem g₁⟩ _ tie x', h2 s hμ k _ (avgK_comm _ _) _ (fun y => (hc y).1) x']
      refine Fintype.sum_equiv ((MulAut.conj c).toEquiv.trans (R.eG.trans cG).toEquiv) _ _ fun y => ?_
      rw [(hc y).2, inv_one, mul_one, ← avgK_conj _ _ c y, tie, ← map_mul]
      rfl
    exact LinearMap.congr_fun hF x
  apply (ad.eW _ hμ k).injective
  rw [ad.read, map_sum]
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV k).W :=
    { toFun := fun z' => adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z' x) ((ad.PV k).ψ g)
      map_add' := fun y y' => by simp only [map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c y => by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  refine (lin_center Φ (fun g₀ => adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀))) key z).trans ?_
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [map_smul, ad.read]
  rfl

end Rows

end GlobalTheory.CenLocAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.CenIntAtLoc

open Formalism.L2.DIV

theorem mapCoef_mem_center {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : ∀ a, z * a = a * z) :
    Formalism.MainNotions.PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    have e : MonoidAlgebra.of S G m = MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of R G m) := by
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
    rw [e]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem coeff_mapCoef {R S M : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : MonoidAlgebra R M) (m : M) :
    (Formalism.MainNotions.PairedCharacterCondition.mapCoef f z).coeff m = f (z.coeff m) := by
  simp [Formalism.MainNotions.PairedCharacterCondition.mapCoef]

theorem cenInt_of_allT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G}
    {ψ1 : P1 →* D.what₂.LLˣ} {X0 : BaseLevelRowSide D} {tp : D.what₂.Tup → T} {eG : G ≃* G0g D.nd}
    (h : AllT D A P0 ψ0 P1 ψ1 X0 tp eG) (v : InfinitePlace D.what₂.LL) (hv : Formalism.DivisionValues.IsConjAt v)
    (hpos : ∀ k τ, ((A.fam.L k τ).S.H.map v.embedding).PosDef)
    (hact : ∀ k τ, (A.fam.L k τ).S.ActGood (A.fam.L k τ).r) : GlobalTheory.PendOf.CenInt D := by
  intro i z hz x hx
  have hc := mapCoef_mem_center (Int.castRingHom ℂ) z hz
  have key : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ x ∈ GlobalTheory.EtaJoin.genSet D μ j,
      ∃ y ∈ GlobalTheory.EtaJoin.lat D μ j, D.what₂.jMt μ j y = D.ntypes.cenMt μ j ⟨_, hc⟩ (D.what₂.jMt μ j x) := by
    intro μ j h1 h2 x hx
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
    let a : MonoidAlgebra D.what₂.LL G :=
      MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm (Formalism.MainNotions.PairedCharacterCondition.mapCoef (Int.castRingHom D.what₂.LL) z)
    have hcoef : ∀ g : G, a.coeff g = ((z.coeff (eG g) : ℤ) : D.what₂.LL) := by
      intro g
      simp [a, coeff_mapCoef]
    have ha : ∀ g : G, D.what₂.embLL (a.coeff g) =
        ((⟨_, hc⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g) := by
      intro g
      rw [hcoef g]
      simp [coeff_mapCoef]
    have hcL := mapCoef_mem_center (Int.castRingHom D.what₂.LL) z hz
    have hac : ∀ b, a * b = b * a := by
      intro b
      obtain ⟨b', rfl⟩ := (MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm).surjective b
      simp only [a, ← map_mul]
      rw [Subalgebra.mem_center_iff.mp hcL b']
    have hint : ∀ t : G, ∃ n : ℤ, a.coeff t = n := fun t => ⟨_, hcoef t⟩
    obtain ⟨-, -, h3⟩ := h.cen μ ⟨_, hc⟩ a ha
    classical
    have h3' := h3 k ((h.eMt k μ).symm x)
    rw [LinearEquiv.apply_symm_apply] at h3'
    obtain ⟨hgen, hlat⟩ := h.latL k μ
    have hx' : (h.eMt k μ).symm x ∈ lNab D A P0 ψ0 k (tp μ) := by
      rw [hlat]
      refine ⟨fun v => if v = D.what₂.jMt μ ((k : ℕ) + 1) x then 1 else 0, ?_⟩
      have hxg : D.what₂.jMt μ ((k : ℕ) + 1) x ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen := hx
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
      rw [Finset.sum_eq_single_of_mem _ hxg]
      · simp
      · intro b _ hb
        simp [hb]
    have hy' := GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms D.what₂.LL v hv (A.fam.L k (tp μ)).S (hpos k (tp μ)) G (A.fam.L k (tp μ)).r (hact k (tp μ))
      (A.fam.lvlA P0 ψ0).P (A.fam.lvlA P0 ψ0).ψ a hac hint _ hx'
    obtain ⟨c, hc'⟩ := (hlat _).mp hy'
    have hsrc : ∀ u : (D.what₂.MtLat μ ((k : ℕ) + 1)).gen, ∃ w, D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ w) = u.1 := by
      intro u
      obtain ⟨w, hw⟩ := hgen u.1 u.2
      exact ⟨w, hw⟩
    choose ws hws using hsrc
    refine ⟨∑ u ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen.attach, c u.1 • h.eMt k μ (ws u), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      show D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ (ws u)) ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen
      rw [hws u]
      exact u.2
    · rw [h3']
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hc'
      rw [hc', map_sum, ← Finset.sum_attach (D.what₂.MtLat μ ((k : ℕ) + 1)).gen]
      refine Finset.sum_congr rfl fun u _ => ?_
      have e1 : c u.1 • h.eMt k μ (ws u) = ((c u.1 : 𝓞 D.what₂.LL) : D.what₂.LL) • h.eMt k μ (ws u) := rfl
      rw [e1, LinearMap.map_smulₛₗ, hws u]
  obtain ⟨y, hy, hyx⟩ := key (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 x hx
  refine ⟨y, hy, ?_⟩
  rw [hyx]
  unfold NTypes.onMt
  rw [dif_pos hc]

end GlobalTheory.CenIntAtLoc

namespace GlobalTheory.CenIntAtLoc

theorem cenInt_at (hL : GlobalTheory.Published.LocalLanglandsGL) :
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ w Z _ _ t _ _ _ _ _ hR _ => ?_
  obtain ⟨r⟩ := hR
  refine cenInt_of_allT r.all (InfinitePlace.mk (w.st Z).B.embLL) (GlobalTheory.Mem.R3.OkVals.isConjAt_embLL _) (fun k τ => ?_) (fun k τ => ?_)
  · exact (Formalism.L2.Col.mtK_rat _ _ _ τ.1 t.hX ((k : ℕ) + 1)).posH _ _
  · exact Formalism.L2.Col.unipotentActionClassSum_good _ _ _ τ.1 t.hX ((k : ℕ) + 1) _

end GlobalTheory.CenIntAtLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem depth_le_starDepth : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → 0 ≤ t → B - t • toReal v ∈ rcone γ → t ≤ evalR (starDepth bar ψ w) B := by
  intro O _ bar ψ w X _ _ _ m γ B v t hγ hB hv hvp hvw hvc hv0 huniq ht hBt
  rcases ht.eq_or_lt with rfl | ht
  · exact starDepth_eval_nonneg _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O X
  show t ≤ (starDepth bar ψ w).eval X (fun a b => B a b)
  rw [InvFun.eval_eq _ hπ]
  exact le_csSup (GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre O bar ψ w X m γ B v hγ hB hv hvp hv0 huniq n π hπ)
    (GlobalTheory.T.mem_starDepthSet_through_radicalFree_presentation O bar ψ w X m γ B v t hγ hB hv hvp hvw hvc ht hBt n π hπ)

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnipotent
section
namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem char_eq_one_of_sq_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  intro E _ _ _ N X hE φ γ hγ
  set A : Matrix (Fin N) (Fin N) E := ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) with hA
  set n : Matrix (Fin N) (Fin N) E := A - 1 with hn
  have h2 : n * n = 0 := by rw [← pow_two]; exact hγ
  have hiso : IsIsom X.Gm A := fun x y => (X.Γ_stab _ γ.2).1 x y
  have hsk : IsSkew X.Gm n := isSkew_sub_one X.Gm hiso h2
  set W : Submodule E (Fin N → E) := LinearMap.range (Matrix.mulVecLin n) with hW
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, herm X.Gm u v = 0 := by
    rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
    exact herm_mulVec_mulVec_eq_zero X.Gm hsk h2 x y
  have hκ : cc X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc_mul, cc_neg, X.ξ0_im, cc_two]
  have hκ0 : X.κ0 ≠ 0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  obtain ⟨d, ξ, t, hξW, ht, hnd⟩ := GlobalTheory.T.skew_eq_sum_rank_one_isotropic E N X.Gm X.κ0 X.Gm_herm X.Gm_det hκ hκ0 W hWiso n hsk
    (fun y => ⟨y, rfl⟩)
  obtain ⟨k, ξ', s, hk, hξ'Λ, hξ'a, hs, hsint, hsum⟩ := GlobalTheory.T.sum_rank_one_integral_rescaling E N X d ξ t ht
  have horth : ∀ i j, herm X.Gm (ξ' i) (ξ' j) = 0 := by
    intro i j
    obtain ⟨a, ha⟩ := hξ'a i; obtain ⟨b, hb⟩ := hξ'a j
    rw [ha, hb, herm_smul_left, herm_smul_right, hWiso _ (hξW i) _ (hξW j)]; ring
  have hkill : ∀ j, ∃ γ' : X.Γ, ((γ' : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ' j) (X.m * s j * X.κ0) ∧ φ γ' = 1 := by
    intro j
    obtain ⟨γ', hγ'Γ, hγ'⟩ := X.transv (ξ' j) (hξ'Λ j) (horth j j) (s j) (hs j) (hsint j)
    exact ⟨⟨γ', hγ'Γ⟩, hγ', GlobalTheory.T.character_trivial_on_integral_transvections E N X hE φ (ξ' j) (s j) (hξ'Λ j) (horth j j) (hs j) (hsint j) ⟨γ', hγ'Γ⟩ hγ'⟩
  obtain ⟨γ', hγ'eq, hφγ'⟩ := GlobalTheory.T.character_trivial_on_sum_transvections E N X φ d ξ' (fun j => X.m * s j * X.κ0) horth hkill
  have hpow : γ ^ k = γ' := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hγ'eq, ← hsum, ← hnd]
    have : (γ : GL (Fin N) E).val = 1 + n := by rw [hn]; abel
    rw [this, one_add_pow_of_sq_eq_zero h2]
  have hφ : φ γ ^ k = 1 := by rw [← map_pow, hpow, hφγ']
  have : k • Multiplicative.toAdd (φ γ) = 0 := by
    have := congrArg Multiplicative.toAdd hφ
    rwa [toAdd_pow, toAdd_one] at this
  have h0 := (smul_eq_zero.1 this).resolve_left hk.ne'
  exact Multiplicative.toAdd.injective (by simpa using h0)
end GlobalTheory.UnipKill
end

