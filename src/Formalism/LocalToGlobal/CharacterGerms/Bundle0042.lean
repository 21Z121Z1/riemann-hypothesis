import Formalism.LocalToGlobal.CharacterGerms.Bundle0040
import Formalism.LocalToGlobal.CharacterGerms.LinearPartUnitFrobenius
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroMultiplicationPair
import Formalism.LocalToGlobal.CharacterGerms.Bundle0041
import Formalism.LocalToGlobal.CharacterGerms.Bundle0037
import Formalism.LocalToGlobal.CharacterGerms.RowTieValL
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfUnconditional
section
set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

theorem rank_maximal_self_unconditional : RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_of_eigen first_vanishing_core funEqCore_holds curve_linear_term_unconditional aLinAdj_holds RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTDone
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace TCoord

open Formalism.IncomingBounds FormalGermZero GeneralGermZero

variable {C : Type} [Field C] {κ : Type} [Fintype κ]

theorem tcoord_abs {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ) (g : Fin 2)
    (w : κ → I g → C) (hwI : ∀ x c, V.Ge 0 (w x c))
    (hw : ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (tan : I g → I g → C) (hun : V.v (Matrix.of tan).det = 0)
    (P : κ → MvPowerSeries (I g) C) (hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0) (hPI : ∀ j, IntS V (P j))
    (hPlin : ∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * tan c c')
    (t : I g → MvPowerSeries (I g) C) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hPt : ∀ j, MvPowerSeries.subst t (P j) =
      MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j))
    (c : I g) :
    ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t c) := by

  set E : κ → MvPowerSeries (I g) C := fun j =>
    MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) with hE
  have hE0 : ∀ j, MvPowerSeries.constantCoeff (E j) = 0 := fun j => by
    rw [hE]; simp only; rw [← hPt j]; exact constantCoeff_subst_zero ht0 (hP0 j)
  have hlin0 : ∀ i : κ, MvPowerSeries.constantCoeff
      (∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) = 0 := fun i => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hXg : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => MvPowerSeries.constantCoeff_X _
  have hupE : ∀ j, X.expPt g j = upG g (E j) := by
    intro j
    show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (E j)
    rw [hE]
    simp only
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0) hXg]
    unfold RawChart.expPt
    congr 1
    funext i
    rw [← MvPowerSeries.coe_substAlgHom hXg, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hXg, MvPowerSeries.subst_X hXg]

  set φ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • P j with hφ
  set t₂ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • E j with ht₂
  have hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0 := fun k => by
    rw [hφ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hP0 j, smul_zero]
  have ht₂0 : ∀ k, MvPowerSeries.constantCoeff (t₂ k) = 0 := fun k => by
    rw [ht₂]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hE0 j, smul_zero]
  have hφI : ∀ k, IntS V (φ k) := fun k μ => by
    rw [hφ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (hPI j μ)
  have hL : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)) = (Matrix.of tan).transpose := by
    ext k c
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, hφ]
    simp only
    rw [map_sum]
    simp only [MvPowerSeries.coeff_smul, hPlin]
    have e : ∑ j, w j k * ∑ c', X.u g c' j * tan c c' = ∑ c', tan c c' * ∑ j, X.u g c' j * w j k := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp only [hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have ht₂s := MvPowerSeries.hasSubst_of_constantCoeff_zero ht₂0
  have heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (MvPowerSeries.X k : MvPowerSeries (I g) C) := by
    intro k
    rw [MvPowerSeries.subst_X ht₂s, hφ, ht₂]
    simp only
    rw [← MvPowerSeries.coe_substAlgHom hts, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hts, hPt]
    rfl
  obtain ⟨h, hh0, hhI, hth⟩ := AbstractGermZero.one_group V t t₂ φ (fun k => MvPowerSeries.X k) ht₂0 ht0 hφ0 hφI
    (by rw [hL, Matrix.det_transpose]; exact hun) (fun k => MvPowerSeries.constantCoeff_X k) (fun k => intS_X k) heq

  set ℓ : I g → MvPowerSeries κ C := fun k => ∑ j, w j k • (MvPowerSeries.X j : MvPowerSeries κ C) with hℓ
  have hℓ0 : ∀ k, MvPowerSeries.constantCoeff (ℓ k) = 0 := fun k => by
    rw [hℓ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hℓI : ∀ k, IntS V (ℓ k) := fun k μ => by
    rw [hℓ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (intS_X j μ)
  have hpt0 : ∀ x, MvPowerSeries.constantCoeff (X.expPt g x) = 0 := fun x => by
    rw [hupE x]
    exact constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hE0 x)
  have hpts := MvPowerSeries.hasSubst_of_constantCoeff_zero hpt0
  refine ⟨MvPowerSeries.subst ℓ (h c), IntS.subst hℓ0 hℓI (hhI c), constantCoeff_subst_zero hℓ0 (hh0 c), ?_⟩
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hℓ0) hpts, hth c]
  show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C))
    (MvPowerSeries.subst t₂ (h c))
  rw [MvPowerSeries.subst_comp_subst_apply ht₂s hXg]
  congr 1
  funext k
  rw [hℓ, ht₂]
  simp only
  rw [← MvPowerSeries.coe_substAlgHom hpts, map_sum, ← MvPowerSeries.coe_substAlgHom hXg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, MvPowerSeries.coe_substAlgHom hpts, MvPowerSeries.subst_X hpts,
    MvPowerSeries.coe_substAlgHom hXg, hupE j]
  rfl

theorem tcoord_gen {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
    (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
    (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
    (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.TCoordSt H := by
  intro S t ht g c
  obtain ⟨w, hwI, hw⟩ := hsat g
  obtain ⟨P, hP0, hPI, hPlin, hPt⟩ := sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  exact tcoord_abs X g w hwI hw (S g).tan (S g).unimod P hP0 hPI hPlin (t g) (ht g).1 (hPt (t g) (ht g)) c

end TCoord

def TCoordSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc

theorem tcoordFB_holds : AllFB fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc := by
  unfold AllFB
  intro C _ _ V O _ _ dd Y d _ I _ p H S t ht g c
  obtain ⟨w, hwI, hw⟩ := p.u_sat g
  obtain ⟨P, hP0, hPI, hPlin, hPt⟩ := FormalGermZero.sys_P Y p (H g) (S g)
  exact TCoord.tcoord_abs (Y.raw p) g w hwI hw (S g).tan (S g).unimod P hP0 hPI hPlin (t g) (ht g).1
    (hPt (t g) (ht g)) c

theorem tcoordSelf_holds : TCoordSelfSt := by
  unfold TCoordSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact TCoord.tcoord_gen (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y) (SelfConjugateGermZero.lgS_add Y p)
    (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (SelfConjugateGermZero.sat_self Y p) H

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def GeoJ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (OE : Type) [CommRing OE] [StarRing OE] (aG : OE → (G ⟶ G)) (dd : ℕ) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∃ (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (F : FGLaw T dd)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin dd) m) ⟶ G) (_ : Module OE D.toPre.X) (io : Out.RingAct G OE)
    (oD : D.OAct OE) (oA : A.OAct OE) (act : Germ.OAct OE F),
    F.F = FT ∧ act.act = actT ∧ (∀ a, io.act a = aG a) ∧ IsChartJ G F x ∧ U.OLinear OE oD oA io ∧
      ChartActs G x io act

def PlaceIn (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ (w : PlaceU l OE) (_ : NeZero w.n) (t : Fin w.n ≃ Emb (O := R) w.e) (jj : ZMod d ≃ Fin w.n),
    (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : Emb (O := R) w.e) : OE →+* R) = em a) ∧
    ∃ b : Module.Basis (Fin w.n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := R) w.e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def UpFLaw (p : ℕ) [Fact p.Prime] (T : Type) [CommRing T] (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ)
    (FT : Fin dd → PS T 2 dd) (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
    ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
    (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
    (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
        (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
    ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin dd → O),
      (∀ τ, IsEigBasis (fun a i => MvPowerSeries.map iota (actT a i)) τ (W τ)) →
    ∀ j : Fin w.n, ∃ xs : NNReal,
      HasAF v (fun i => MvPowerSeries.map iota (FT i)) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
      v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
        (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
          ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs

theorem upFLaw_of_geoJ {p : ℕ} [Fact p.Prime] (hUp : UpFSt p) (hp2 : p ≠ 2)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit (p : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    {OE : Type} [CommRing OE] [StarRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (aG : OE → (G ⟶ G)) {dd : ℕ} (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (hdisc : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UpFLaw p T OE dd FT actT := by
  obtain ⟨D, A, U, F, x, iM, io, oD, oA, act, rfl, rfl, -, hx, hO, hA⟩ := hG
  intro C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hbas hfrob r W hW j
  exact hUp T hlT G D A U dd F x hx hp2 OE io oD oA hO hdisc act hA C v O hv iota hloc w t hbas hfrob r W hW j

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def EigIn {Y : FBChart C V OE dd} (p : PairData Y d I) (R : Type) [CommRing R] [Algebra R C]
    (actR : OE → Fin dd → PS R 1 dd) (emR : Fin 2 → ZMod d → OE →+* R) : Prop :=
  ∃ (r : (OE →+* R) → ℕ) (W : ∀ τ : OE →+* R, Fin (r τ) → Fin dd → R), (∀ τ, IsEigBasis actR τ (W τ)) ∧
    ∀ g a, ∃ e : Fin (r (emR g a)) ≃ {x : I g // p.ty g x = a},
      ∀ c i, algebraMap R C (W (emR g a) c i) = p.u g (e c) i

theorem ofNat_succ (n : ℕ) [NeZero n] (k : ℕ) : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem jj_add {n : ℕ} [NeZero n] (jj : ZMod d ≃ Fin n) (h : ∀ a, jj (a + 1) = jj a + 1) (a : ZMod d) :
    ∀ k : ℕ, jj (a + (k : ZMod d)) = jj a + Fin.ofNat n k
  | 0 => by
    have : Fin.ofNat n 0 = 0 := by apply Fin.ext; simp [Fin.ofNat]
    simp [this]
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, h, jj_add jj h a k, ofNat_succ, add_assoc]

theorem afBound_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : vm.Integers R)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) :
    AFBound Y p vm R (fun i => MvPowerSeries.map iota (FT i)) := by
  have := Y.algClosed
  intro g a _
  obtain ⟨w, iN, t, jj, hj1, hjt, hbas⟩ := hPl g
  obtain ⟨r, W, hW, hWe⟩ := hEig
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hfrob : ∀ (j : Fin w.n) (x : OE), ((t (j + 1) : Emb (O := R) w.e) : OE →+* R) x -
      (((t j : Emb (O := R) w.e) : OE →+* R) x) ^ V.l ∈ maximalIdeal R := by
    intro j x
    obtain ⟨a', rfl⟩ := jj.surjective j
    rw [← hj1, hjt, hjt]
    apply hMM
    rw [map_sub, map_pow, hem, hem]
    exact p.em_frob g a' x
  obtain ⟨xs, hAF, hle⟩ := hL C vm R hv iota hloc w t hbas hfrob r W hW (jj a)
  obtain ⟨e, he⟩ := hWe g a
  have hconj : ∀ b, (emR g b).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom = emR (1 - g) b := by
    intro b
    ext x
    apply hinj
    show algebraMap R C (emR g b (star x)) = _
    rw [hem, hem]
    fin_cases g
    · exact (p.em_conj b x).symm
    · show p.em 1 b (star x) = p.em 0 b x
      rw [p.em_conj, star_star]
  have hrk : ∀ b, r (emR (1 - g) b) = rk p (1 - g) b := by
    intro b
    obtain ⟨e', -⟩ := hWe (1 - g) b
    have := Fintype.card_congr e'
    rw [Fintype.card_fin, Fintype.card_subtype] at this
    exact this
  refine ⟨r (emR g a), e, W (emR g a), xs, he, ?_, ?_⟩
  · rw [hjt a] at hAF
    exact hAF
  · have hs : S4.frobSum V.l (rk p (1 - g)) a = ∑' n : ℕ, ((V.l : ℝ) ^ (-((n : ℝ) + 1))) *
          (r (((t (jj a + Fin.ofNat w.n (n + 1)) : Emb (O := R) w.e) : OE →+* R).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ) := by
      unfold S4.frobSum
      refine tsum_congr fun n => ?_
      rw [← jj_add jj hj1 a (n + 1), hjt, hconj, hrk, rpow_neg_succ V.l_prime.pos]
    rw [hs]
    rw [map_natCast] at hle
    exact hle

theorem upChar_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hT : ValTie V vm) (hv : vm.Integers R)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (hF : ∀ i, Y.B.G.F i = toC (MvPowerSeries.map iota (FT i)))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) : UPCharSt Y p Hc := by
  refine upChar_of_afBound Y p hr Hc vm R hT hv h0 h1 (fun i => MvPowerSeries.map iota (FT i)) hF ?_
    (afBound_of_upFLaw Y p vm R hv hMM T FT actT hL iota hloc emR hem hPl hEig)
  intro i
  apply hv.hom_inj
  have := Y.B.G.const i
  rw [hF i, MvPowerSeries.constantCoeff_map] at this
  rw [this, map_zero]

theorem upChar_of_upF [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hUp : UpFSt V.l) (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hT : ValTie V vm) (hv : vm.Integers R)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit ((V.l : ℕ) : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (aG : OE → (G ⟶ G)) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (hF : ∀ i, Y.B.G.F i = toC (MvPowerSeries.map iota (FT i)))
    (hdisc : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) : UPCharSt Y p Hc :=
  upChar_of_upFLaw Y p hr Hc vm R hT hv h0 h1 hMM T FT actT
    (upFLaw_of_geoJ hUp Y.l_odd T hlT G aG FT actT hG hdisc) iota hloc hF emR hem hPl hEig

end Inst

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValU
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0

theorem IsIU.one {σ : Type} : IsIU V (1 : MvPowerSeries σ C) := by
  refine ⟨fun μ => ?_, ?_⟩
  · unfold VF.Ge
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [AddValuation.map_one]; exact le_rfl
    · rw [AddValuation.map_zero]; exact le_top
  · rw [map_one, AddValuation.map_one]

theorem IsIU.mul {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩

theorem IsIU.prod {σ ι : Type} (s : Finset ι) {U : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IsIU V (U i)) :
    IsIU V (∏ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact IsIU.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

structure IsProj (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : Prop where
  int : ∀ o g i, IntS V (π o g i)
  cc : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0
  pull : ∀ o g i, pull1 Y p (π o g i) = toAllS o ((Y.raw (p o)).expPt g i)

def Aterm (π : Orb → Fin 2 → Fin dd → PS C 1 dd) (s s' : Orb × Fin 2) : PS C 1 dd :=
  FB.expS C ((Y.k : C) • ev (n := 1) ![π s.1 s.2, comp1 (Y.B.actK C Y.w0) (π s'.1 s'.2)] Y.h)

def barS (s : Orb × Fin 2) : Orb × Fin 2 := (s.1, 1 - s.2)

def BiaddSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, pull1 Y p (Aterm Y π s s')

def CrossSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ s s' : Orb × Fin 2, s' ≠ barS s →
    ∃ U : PS C 1 dd, IsIU V U ∧ pull1 Y p (Aterm Y π s s') = pull1 Y p U

def PairSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ o : Orb, ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (Aterm Y π (o, 0) (o, 1)) * pull1 Y p (Aterm Y π (o, 1) (o, 0)) =
      pull1 Y p U * toAllS o (mvExp (Y.raw (p o)).hRow)

end Defs

theorem unit_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hP : ProjPullSt Y p) (h1 : BiaddSt Y p)
    (h2 : CrossSt Y p) (h3 : PairSt Y p) : UnitSt Y p := by
  intro hs
  choose π hπi hπc hπp using hP hs
  have hproj : IsProj Y p π := ⟨hπi, hπc, hπp⟩
  obtain ⟨U0, hU0, hE⟩ := h1 hs π hproj
  choose Uc hUc hUceq using h2 hs π hproj
  choose Up hUp hUpeq using h3 hs π hproj

  let W : Orb × Fin 2 → Orb × Fin 2 → PS C 1 dd := fun s s' =>
    if h : s' ≠ barS s then Uc s s' h else 1
  have hW : ∀ s s', IsIU V (W s s') := by
    intro s s'
    by_cases h : s' ≠ barS s
    · simp only [W, dif_pos h]; exact hUc s s' h
    · simp only [W, dif_neg h]; exact IsIU.one
  have hone : pull1 Y p (1 : PS C 1 dd) = 1 := by
    have := VP.pullback_one_var_prod (Y := Y) (p := p) (∅ : Finset Unit) (fun _ => 1)
    simpa using this
  have hA : ∀ s s', pull1 Y p (Aterm Y π s s') =
      pull1 Y p (W s s') * (if s' = barS s then pull1 Y p (Aterm Y π s (barS s)) else 1) := by
    intro s s'
    by_cases h : s' = barS s
    · have h' : ¬ s' ≠ barS s := not_not.2 h
      simp only [W, dif_neg h', if_pos h, hone, one_mul]
      rw [h]
    · simp only [W, dif_pos h, if_neg h, mul_one]
      exact hUceq s s' h
  have hpair : ∏ s : Orb × Fin 2, pull1 Y p (Aterm Y π s (barS s)) =
      ∏ o, (pull1 Y p (Up o) * toAllS o (mvExp (Y.raw (p o)).hRow)) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun o _ => ?_
    rw [Fin.prod_univ_two]
    have hb0 : barS (o, (0 : Fin 2)) = (o, 1) := by simp [barS]
    have hb1 : barS (o, (1 : Fin 2)) = (o, 0) := by simp [barS]
    rw [hb0, hb1]
    exact hUpeq o
  refine ⟨U0 * (∏ s, ∏ s', W s s') * ∏ o, Up o,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).1,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).2, ?_⟩
  rw [hE]
  rw [Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun s' _ => hA s s']
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [hpair, Finset.prod_mul_distrib, VP.pullback_one_var_mul, VP.pullback_one_var_mul, VP.pullback_one_var_prod, VP.pullback_one_var_prod]
  simp_rw [VP.pullback_one_var_prod]
  ring

theorem valuation_eq_pair_of_pairing (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h1 : BiaddSt Y p) (h2 : CrossSt Y p) (h3 : PairSt Y p) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_unit_germ Y p H Ls n (unit_of Y p hP h1 h2 h3) (germLift_of Y p H hP hT)

end Formalism.L2.FormalSeriesBounds
end
end

