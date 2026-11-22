import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLevelPowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_level_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  first | exact @GlobalTheory.FlatModel.tateIso_transport_ptOn | exact GlobalTheory.FlatModel.tateIso_transport_ptOn | (intros; apply GlobalTheory.FlatModel.tateIso_transport_ptOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_pairing_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    (∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃! x : LieG P.Gt, ITie P π x u) ∧
    (∀ x : LieG P.Gt, ∃ u, IsTanAtG Y.t yb u ∧ ITie P π x u) ∧
    (∀ (m : ℕ) (v : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (xs : Fin m → LieG P.Gt) (cf : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left) (x : LieG P.Gt), (∀ i, IsTanAtG Y.t yb (v i)) →
      (∀ i, ITie P π (xs i) (v i)) → IsCombAtG Y.t yb v cf u → ITie P π x u →
      P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)) ∧
    ∀ (σ : 𝓞 E →+* 𝓞_ℂ_[p]) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), IsTanAtG Y.t yb u →
      ITie P π x u → (IsEigG Y.t σ u ↔ AvDefs.IsEig P.Gt P.oGt σ x) := by
  first | exact @GlobalTheory.FlatModel.tanTie | exact GlobalTheory.FlatModel.tanTie | (intros; apply GlobalTheory.FlatModel.tanTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivPointValuationPropertyStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdiv_point_valuation_property : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg →
    ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
      (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C),
      (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) →
      ∀ σ : E →+* ℂ, Module.finrank C (P.eigW (embInt c P.integers σ)) = Dw.mult σ := by
  first | exact @GlobalTheory.CompHt.finrank_eigW_embInt_eq_mult | exact GlobalTheory.CompHt.finrank_eigW_embInt_eq_mult | (intros; apply GlobalTheory.CompHt.finrank_eigW_embInt_eq_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftStOfPublished
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory

theorem placeShiftSt_of_scholzeWeinstein (hP : GlobalTheory.CovTop.Hypotheses2) (hSW : GlobalTheory.Published.ScholzeWeinsteinB) :
    GlobalTheory.FlatCM.PlaceShiftSt :=
  GlobalTheory.T.place_shift_of_dieudonne hSW hP.q4 (GlobalTheory.T.hodge_tate_kernel_at_point hP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have e₂ : cls P hP = evc hP₀ (fst A A) (snd A A ≫ l) :=
    (CechPic.cls_eq_iff hP (pull_isLB hP₀ _)).2 hl
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), evc hP a b = evc hP₀ b (a ≫ l) := by
    intro Y a b
    have h1 : evc hP a b = CechPic.pull (lift a b).left (evc hP (snd A A) (fst A A)) := by
      rw [← e₁]; rfl
    rw [h1, pull_evc, lift_snd, lift_fst]
    change CechPic.pull (lift b a).left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨?_, fun T x hx => ?_⟩
  · refine (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1 ?_
    rw [cls_ev hP, cls_ev (pull_isLB hP₀ _), evc_swap hP₀, key, Category.comp_id]
  · show Triv _
    rw [triv_ev_iff hP, key, Category.assoc, hx, MonObj.comp_one]
    exact evc_one_right hP₀ hD.zero _

end GlobalTheory.AbDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiag
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem posSemidef_real_det_le_prod_diag :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i :=
  fun _ _ hG => GlobalTheory.posSemidef_det_le_prod_diag hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem exists_spMap {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩

theorem unit_left' {S T : Scheme.{0}} {G : Over S} (x : T ⟶ S) (σ : 𝟙_ (Over S) ⟶ G) :
    (toUnit (Over.mk x) ≫ σ).left = x ≫ σ.left := by
  simp

variable {h N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem lev_zero (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem lev_nsmul (C : SiegPre h N ζ s) (k : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (k • a) = C.lev a ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ k ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem lev_N_smul (C : SiegPre h N ζ s) (a : Fin h ⊕ Fin h → ℤ) : C.lev (N • a) = 1 := by
  rw [lev_nsmul, C.lev_tors]

def relabel (C : SiegPre h N ζ s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (σ : B' →+* B)
    (hN : N ≠ 0) (hζ : ζ ^ N = 1) (hσ : σ ζ' = ζ ^ m)
    (hω : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) : SiegPre h N ζ' (s ≫ spMap σ) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev x := C.lev (T x)
  lev_add a b := by rw [map_add, C.lev_add]
  lev_tors a := C.lev_tors _
  geom k _ _ x β z hx hz := by
    obtain ⟨β₀, hβ₀⟩ := exists_spMap (x ≫ s)
    have hb : β = β₀.comp σ := spMap_inj (by rw [← hx, ← Category.assoc, hβ₀, spMap_comp'])
    have h1 : β₀ ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    let z₀ : kˣ := Units.ofPowEqOne (β₀ ζ) N h1 hN
    obtain ⟨g1, g2, g3⟩ := C.geom k x β₀ z₀ hβ₀ rfl
    have hzm : z = z₀ ^ m := Units.ext (by
      rw [hz, hb, RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val]; rfl)
    have hz₀ : z₀ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
    refine ⟨fun a => (g1 (T a)).trans ⟨hinj a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun g hg => ?_,
      fun a b => ?_⟩
    · obtain ⟨a, ha⟩ := g2 g hg
      obtain ⟨a', b, hab⟩ := hsurj a
      refine ⟨a', ?_⟩
      show toUnit _ ≫ C.lev (T a') = g
      rw [hab, C.lev_add, MonObj.comp_mul, lev_N_smul, MonObj.comp_one, _root_.mul_one, ha]
    · have e : z₀ ^ (2 * omegaStd (T a) (T b)) = z ^ (2 * omegaStd a b) := by
        rw [hzm, ← zpow_natCast, ← zpow_mul]
        refine zpow_eq_zpow_iff_modEq.2 (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hz₀)) ?_)
        have := (hω a b).mul_left 2
        calc 2 * omegaStd (T a) (T b) ≡ 2 * (m * omegaStd a b) [ZMOD N] := this
          _ = m * (2 * omegaStd a b) := by ring
      have := g3 (T a) (T b)
      rw [e] at this
      exact this

section Calc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

def Sq (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (φ : c'.A.left ⟶ c.A.left) : Prop :=
  ∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)

theorem Sq.comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : Sq c' c φ) (m' : Sq c'' c' ψ) :
    Sq c'' c (ψ ≫ φ) := by
  obtain ⟨φ₂, hs, hw⟩ := m
  obtain ⟨ψ₂, hs', hw'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem sRelBy_comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c d' d f φ)
    (m' : SRelBy c'' c' d'' d' f' ψ) : SRelBy c'' c d'' d (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, hs, hl⟩ := m
  obtain ⟨hψ, hs', hl'⟩ := m'
  refine ⟨hψ.comp hφ, Sq.comp (c := c) (c' := c') (c'' := c'') hs hs', fun a => ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

end Calc

section Twist

variable {h n N : ℕ}

structure Twist (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N)
    (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (σ : cycAway N →+* cycAway N) (f : F.X ⟶ F.X) :
    Prop where
  cop : m.Coprime N
  root : σ (zetaAway N) = zetaAway N ^ m
  fix : σ.comp j = j
  symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]
  low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)
  comm : f ≫ F.s = F.s ≫ spMap σ
  map : ∃ ν : F.univ.A.left ⟶ F.univ.A.left, IsGrpPullback F.univ.A F.univ.A f ν ∧ Sq F.univ F.univ ν ∧
    ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left

end Twist

end GlobalTheory.SiegAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDescentFiniteEtaleSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevDescent

theorem principal_of_sRel_finite_etale : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  intro h M M₀ d d₀ B B₀ _ _ ζ ζ₀ X Y _ s s₀ π c c₀ hfin het hsurj m hc
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨(relAmple_kTriv_of_finite_etale_cover Y X π c₀.A c.A φ c₀.diag c.diag hfin het hsurj c₀.ab
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) pb (GlobalTheory.SiegelPull.diag_iso sq iso)).1 h₁, ?_⟩
  intro T x ⟨t, ht⟩
  haveI := het
  haveI := hsurj
  let T' : Over X := Over.mk (pullback.snd T.hom π)
  let p : T'.left ⟶ T.left := pullback.fst T.hom π
  have hp : p ≫ T.hom = T'.hom ≫ π := pullback.condition
  haveI : Epi p := Flat.epi_of_flat_of_surjective _
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom pb T' T p hp
  have hx' : (ρ x).left ≫ φ = p ≫ x.left := (hρ x (ρ x)).1 rfl
  have w₁ : (fst c.A T').left ≫ φ ≫ c₀.A.hom = ((snd c.A T').left ≫ p) ≫ T.hom := by
    rw [pb.1.w, ← Category.assoc, Over.w (fst c.A T'), Category.assoc, hp, ← Category.assoc,
      Over.w (snd c.A T')]
  let χ : (c.A ⊗ T').left ⟶ (c₀.A ⊗ T).left := pullback.lift ((fst c.A T').left ≫ φ) ((snd c.A T').left ≫ p) w₁
  have χ₁ : χ ≫ (fst c₀.A T).left = (fst c.A T').left ≫ φ := pullback.lift_fst _ _ _
  have χ₂ : χ ≫ (snd c₀.A T).left = (snd c.A T').left ≫ p := pullback.lift_snd _ _ _
  have e : (lift (snd c.A T' ≫ ρ x) (fst c.A T')).left ≫ φ₂ = χ ≫ (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left :=
    GlobalTheory.SiegelDescent.lift_square sq (τ := χ)
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc χ, χ₂, Category.assoc])
      χ₁.symm
  have H := GlobalTheory.SiegelDescent.lbIso_square c.isLB c₀.isLB iso e
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullPull (c₀.P.pull (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left) χ) t ht
  have hg := GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB (pull_isLB c₀.isLB _) _) (pull_isLB c.isLB _)
    H.symm ⟨t₁, ht₁⟩
  have h₃ : ρ x = 1 := h₂ T' (ρ x) hg
  have h₄ : p ≫ x.left = p ≫ (1 : T ⟶ c₀.A).left := by
    rw [← hx', h₃, GlobalTheory.SiegelDescent.one_comp pb T' T p hp]
  exact Over.OverMorphism.ext ((cancel_epi p).1 h₄)

end GlobalTheory.SiegLevDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPrim

variable {R : Type} [CommRing R]

theorem pullOver_one_eq_zero {Y A : Over (Sp R)} [GrpObj A] (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (1 : Y ⟶ A) c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]

theorem pullOver_id_apply {A : Over (Sp R)} (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := IsMor.pullCohomologyOne_id _ _

theorem allPrim_of_free (H : GlobalTheory.Published.AbelianDeRhamFree) {A : Over (Sp R)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  obtain ⟨f1, p1, r1, -⟩ := H R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := H R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (GlobalTheory.AbDual.smooth_prod hg hg)
  let r : FirstDeRham ((A ⊗ A).hom ≫ 𝟙 _) →ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) × FirstDeRham (A.hom ≫ 𝟙 _) :=
    (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1)).prod (pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have hv : ∀ x, r x =
      (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1) x, pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)) x) :=
    fun _ ↦ rfl
  have hr : ∀ a b,
      r (pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b) = (a, b) := by
    intro a b
    rw [hv]
    simp only [map_add, pullOver_pullOver, lift_fst, lift_snd, pullOver_one_eq_zero,
      pullOver_id_apply, add_zero, zero_add]
  have hs : Function.Surjective r := fun x ↦ ⟨_, hr x.1 x.2⟩
  have hb : Function.Bijective r :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m _ ↦ by
      rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring
  refine eq_top_iff.2 fun c _ ↦ (mem_prim_iff _ _ A c).2 (hb.1 ?_)
  rw [hr, hv]
  simp only [pullOver_pullOver, ← Hom.mul_def, _root_.mul_one, _root_.one_mul, pullOver_id_apply]

theorem abelianDeRham_free (H : GlobalTheory.Published.AbelianDeRhamFree) : GlobalTheory.Published.AbelianDeRham.Free :=
  fun R _ A _ g hA hg ↦ ⟨allPrim_of_free H hA hg, H R A g hA hg⟩

end GlobalTheory.AbelianPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackGroupPointToModelGroupLinearCombinationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackGroupPointToModelGroup_linearCombination : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G)) (ub' : Fin m → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G) (a : Fin m → V) (w : epsOver V V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) → (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → IsComb ub a w → ∑ i, a i • ub' i = v := by
  first | exact @GlobalTheory.TanComb.tanComb | exact GlobalTheory.TanComb.tanComb | (intros; apply GlobalTheory.TanComb.tanComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackSection_integralValue_dualPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  first | exact @GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull | exact GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull | (intros; apply GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull <;> assumption)
end

