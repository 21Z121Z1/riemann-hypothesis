import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.TransportUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {A : Type} [CommRing A]

theorem exists_inv {m n : ℕ} {x : Matrix (Fin m) (Fin n) A}
    (h : Function.Bijective (x.mulVec : (Fin n → A) → (Fin m → A))) :
    ∃ y : Matrix (Fin n) (Fin m) A, y * x = 1 ∧ x * y = 1 := by
  let e : (Fin n → A) ≃ₗ[A] (Fin m → A) := LinearEquiv.ofBijective (Matrix.toLin' x) h
  have hx : x = LinearMap.toMatrix' e.toLinearMap := (LinearMap.toMatrix'_toLin' x).symm
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp

theorem hform_mulVec (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (k *ᵥ a) = (σ ∘ a) ᵥ* Formalism.UG.cT σ k := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem unitary_iff (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT σ k * J * k = J ↔ ∀ a b, Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ J a b := by
  refine ⟨fun h a b => by rw [hform_mulVec, h], fun h => ?_⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec] at this
  simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using this

theorem smul_eq_of_fix {m n : ℕ} {e : A} (β : GL (Fin m) A) {B : Matrix (Fin m) (Fin n) A}
    {k : Matrix (Fin m) (Fin m) A} (h : ∀ j, ∃ c, e • (β.val *ᵥ Pi.single j 1) = B *ᵥ c) (hk : k * B = B) :
    e • k = e • (1 : Matrix (Fin m) (Fin m) A) := by
  have h1 : k * (e • β.val) = e • β.val := by
    ext i j
    obtain ⟨c, hc⟩ := h j
    have : k *ᵥ (e • (β.val *ᵥ Pi.single j 1)) = e • (β.val *ᵥ Pi.single j 1) := by
      rw [hc, mulVec_mulVec, hk]
    have := congrFun this i
    simpa [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply] using this
  have h2 := congrArg (· * (β⁻¹).val) h1
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using h2

theorem fix_of_smul_eq {m n : ℕ} {e : A} {B : Matrix (Fin m) (Fin n) A} {k : Matrix (Fin m) (Fin m) A}
    (h : e • k = e • (1 : Matrix (Fin m) (Fin m) A)) (hB : e • B = B) : k * B = B := by
  rw [← hB, Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.smul_mul, Matrix.one_mul]

theorem conj_smul_eq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J k : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J)
    (hk : Formalism.UG.cT σ k * J * k = J) {e : A} (he : e • k = e • (1 : Matrix (Fin n) (Fin n) A)) :
    σ e • k = σ e • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : (e • Formalism.UG.cT σ k) * J = (e • (1 : Matrix (Fin n) (Fin n) A)) * J := by
    calc (e • Formalism.UG.cT σ k) * J = Formalism.UG.cT σ k * J * (e • (1 : Matrix (Fin n) (Fin n) A)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by rw [← he, Matrix.mul_smul, hk, he, Matrix.smul_mul, Matrix.one_mul]
  have h2 := hJ.mul_right_cancel h1
  ext i j
  have := congrArg σ (congrFun (congrFun h2 j) i)
  simpa [Formalism.UG.cT, hσ, Matrix.one_apply, apply_ite σ, eq_comm] using this

theorem bc_eq_one_iff {B : Type} [CommRing B] (φ : A →+* B) {n : ℕ} (k : GL (Fin n) A) :
    Formalism.UG.bc φ k = 1 ↔ ∀ i j, φ (k.val i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero]
  simp [Formalism.UG.bc, Matrix.one_apply, apply_ite φ]

end Gen

variable {D : D7}

theorem idem_smul_iff (w : Pl D.host.E) {n : ℕ} (k l : Matrix (Fin n) (Fin n) (EAf D)) :
    idem w • k = idem w • l ↔ ∀ i j, GlobalTheory.StdFrames.cpt w (k i j - l i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero, ← idem_mul_eq_iff]
  rfl

theorem bc_prV_eq_one_iff (w : Pl D.host.E) {n : ℕ} (k : GL (Fin n) (EAf D)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1 ↔
      idem w • k.val = idem w • (1 : Matrix (Fin n) (Fin n) (EAf D)) ∧
      idem (GlobalTheory.IdemSupport.cP w) • k.val = idem (GlobalTheory.IdemSupport.cP w) • (1 : Matrix (Fin n) (Fin n) (EAf D)) := by
  rw [idem_smul_iff, idem_smul_iff]
  refine (bc_eq_one_iff _ k).trans ?_
  have h := fun z => GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (GlobalTheory.StdFrames.toAd_spec D) (w.under (𝓞 D.host.F)) z
  constructor
  · intro H
    exact ⟨fun i j => (h _).1 (H i j) w rfl, fun i j => (h _).1 (H i j) _ (GlobalTheory.IdemSupport.under_cP w)⟩
  · rintro ⟨H1, H2⟩ i j
    refine (h _).2 fun P hP => ?_
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hP with rfl | rfl
    · exact H1 i j
    · exact H2 i j

theorem mem_level_iff (W : HSp D) (L : Lat W) (k : GL (Fin W.rank) (EAf D)) :
    k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ↔
      Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) ∧
        ∀ a, a ∈ hat L ↔ k.val *ᵥ a ∈ hat L := Iff.rfl

theorem col_mem_gen {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (β : GL (Fin n) A) (j i : Fin n) :
    ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) i ∈ S := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem idem_smul_eq_of_fix {W : HSp D} {L : Lat W} (hL : Submodule.IsLattice D.host.E L) {w : Pl D.host.E} {n : ℕ}
    {B : Matrix (Fin W.rank) (Fin n) (EAf D)} (hB : IsBasisAt W w L B) {k : Matrix (Fin W.rank) (Fin W.rank) (EAf D)}
    (h1 : HMul.hMul k B = B) : idem w • k = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  obtain ⟨-, e, he, -, hc⟩ := hB
  obtain rfl := eq_idem he
  obtain ⟨β, rfl⟩ := exists_eq_lat hL
  refine smul_eq_of_fix β (fun j => ?_) h1
  have h := (mem_hat_lat β _).2 (col_mem_gen (OA D) β j)
  obtain ⟨c, hc'⟩ := (hc _).1 ⟨smul_mem_hat (idem_mem w) h, by rw [smul_smul, idem_mul_self]⟩
  exact ⟨_, hc'⟩

theorem transport_unique : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S _ n be be' hL hbe x hx x'
  obtain ⟨⟨hb, hf⟩, hl, hs⟩ := hx
  constructor
  · rintro ⟨⟨hb', hf'⟩, hl', hs'⟩
    obtain ⟨y, y1, y2⟩ := exists_inv hb
    obtain ⟨y', y1', y2'⟩ := exists_inv hb'
    let k : GL (Fin W.rank) (EAf D) := ⟨HMul.hMul y x', HMul.hMul y' x,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', y2', Matrix.one_mul, y1],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x, y2, Matrix.one_mul, y1']⟩
    have hk : HMul.hMul x k.val = x' := by
      change HMul.hMul x (HMul.hMul y x') = x'
      rw [← Matrix.mul_assoc, y2, Matrix.one_mul]
    have hkv : ∀ a, x *ᵥ (k.val *ᵥ a) = x' *ᵥ a := fun a => by rw [mulVec_mulVec, hk]
    have hU : Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) :=
      (unitary_iff _ _ _).2 fun a b => by
        rw [← hA_eq, ← hA_eq, ← hf, hkv, hkv, hf']
    refine ⟨k, ⟨(mem_level_iff W L k).2 ⟨hU, fun a => ?_⟩, fun w hw => ?_⟩, hk.symm⟩
    · rw [hl (k.val *ᵥ a), hkv, hl']
    · have h1 : HMul.hMul k.val (be w) = be w := by
        change HMul.hMul (HMul.hMul y x') (be w) = be w
        rw [Matrix.mul_assoc, hs' w hw, ← hs w hw, ← Matrix.mul_assoc, y1, Matrix.one_mul]
      have h2 : idem w • k.val = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) :=
        idem_smul_eq_of_fix hL (hbe w hw) h1
      refine (bc_prV_eq_one_iff w k).2 ⟨h2, ?_⟩
      rw [← cjA_idem]
      exact conj_smul_eq (cjA D) cjA_cjA (GlobalTheory.StdFrames.isUnit_gram W) hU h2
  · rintro ⟨k, ⟨hk, hk1⟩, rfl⟩
    obtain ⟨hU, hst⟩ := (mem_level_iff W L k).1 hk
    refine ⟨⟨?_, fun a b => ?_⟩, fun a => ?_, fun w hw => ?_⟩
    · have : (HMul.hMul x k.val : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)).mulVec = x.mulVec ∘ k.val.mulVec := funext fun a => (mulVec_mulVec _ _ _).symm
      rw [this]
      refine hb.comp (Function.bijective_iff_has_inverse.2 ⟨(k⁻¹).val.mulVec, fun a => ?_, fun a => ?_⟩)
      · rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, hf, hA_eq, hA_eq]
      exact (unitary_iff _ _ _).1 hU b a
    · rw [← mulVec_mulVec, ← hl, ← hst]
    · obtain ⟨-, e, he, hB, -⟩ := hbe w hw
      obtain rfl := eq_idem he
      have h2 := ((bc_prV_eq_one_iff w k).1 (hk1 w hw)).1
      have h3 : HMul.hMul k.val (be w) = be w := fix_of_smul_eq h2 hB
      rw [Matrix.mul_assoc, h3, hs w hw]

end GlobalTheory.TransportUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjGroup

open Classical Formalism.L2.SG.HidaSetting

abbrev II (D : D7) : AutInst := Formalism.L2.SG.InstExistsPf.instOf D

section Red
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def redV (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → kP PP :=
  fun i => if h : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _).mulVec v i ∈
      Formalism.L2.Herm.intAf F E then resS F PP ⟨_, h⟩ else 0

end Red

def basisOrRevDual {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then b else fun i => bd (Fin.rev i)

def dualOrRevBasis {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then bd else fun i => b (Fin.rev i)

def LocAt {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D))
    (ew : EAf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool) : Prop :=
  ((g : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP ⟨ew, h1⟩ = if w then 1 else 0) ∧
    (∀ h1 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      resS D.host.F PP ⟨sigA (II D) ew, h1⟩ = if w then 0 else 1) ∧
    RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0)

end GlobalTheory.SeeConjGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctionalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_handedDown_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  first | exact @GlobalTheory.HandTame.handP₂ | exact GlobalTheory.HandTame.handP₂ | (intros; apply GlobalTheory.HandTame.handP₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

variable {D : D7}

def resT (PP : Pl D.host.E) (x : EAf D) : kP PP :=
  if hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ else 0

def hT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
    (Formalism.L2.SG.HidaSetting.hA X.B.I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) x)
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) y))

def argT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (M : GL (Fin (Yc D 0).rank) (EAf D)) : EAf D :=
  (∑ a, hT X h (f0T X h a) (Matrix.mulVec M.val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) +
    ∑ i : Fin D.R.k, if hi : i.1 + 1 < D.R.k then
      hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h ⟨i.1 + 1, hi⟩)) else 0

def sideAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) : Bool :=
  decide (GlobalTheory.StdFrames.cpt PP (ewT X h) = 1)

def wA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem conjPrime_asIdeal (PP : Pl D.host.E) :
    (GlobalTheory.IdemSupport.cP PP).asIdeal = PP.asIdeal.map (GlobalTheory.IdemSupport.cO D) := by
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    exact ⟨GlobalTheory.IdemSupport.cO D x, hx, GlobalTheory.IdemSupport.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [GlobalTheory.IdemSupport.cO_cO]
    exact hy

def conjRes (PP : Pl D.host.E) : kP PP ≃+* kP (GlobalTheory.IdemSupport.cP PP) :=
  Ideal.quotientEquiv _ _ (GlobalTheory.IdemSupport.cO D) (conjPrime_asIdeal PP)

end GlobalTheory.SeeConjChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFixStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSplitting_unramified_hyperspecial_fix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  first | exact @GlobalTheory.ConjVacFix.unr_and_vacFix | exact GlobalTheory.ConjVacFix.unr_and_vacFix | (intros; apply GlobalTheory.ConjVacFix.unr_and_vacFix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwiner_values_smoothAutomorphic : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  first | exact @GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | exact GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | (intros; apply GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl UA)
open Formalism.L2.Theta (GA GfC finHom frameMat)
open Formalism.IndefR.Lev (EAf finE)
open Formalism.IndefR.Datum (IsSelfDualC)
open Formalism.UG (cT hform)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsomCorrection

section Algebra

variable {A : Type} [CommRing A] (σ : A →+* A)

theorem cT_mul_rect {l m n : ℕ} (M : Matrix (Fin l) (Fin m) A) (N : Matrix (Fin m) (Fin n) A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, Matrix.map_mul, transpose_mul]
  rfl

theorem gram_of_form {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x : Matrix (Fin m) (Fin n) A)
    (h : ∀ i j, hform σ J' (x *ᵥ Pi.single i 1) (x *ᵥ Pi.single j 1) = J i j) :
    cT σ x * J' * x = J := by
  ext i j
  rw [← h i j]
  simp only [hform, mulVec_single_one, Matrix.mul_apply, cT, transpose_apply, map_apply, col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem exists_unitary {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) (y' : Matrix (Fin n) (Fin m) A) (h1 : y * y' = 1) (h2 : y' * y = 1)
    (hb : Function.Surjective x.mulVec) (hx : cT σ x * J' * x = J) (hy : cT σ y * J' * y = J) :
    ∃ g : GL (Fin m) A, cT σ g.1 * J' * g.1 = J' ∧ g.1 * y = x := by
  have hu : IsUnit (x * y') := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w, rfl⟩ := hb v
    exact ⟨y *ᵥ w, by rw [mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec, cT_mul_rect]
    have e : cT σ y' * cT σ y = 1 := by
      rw [← cT_mul_rect, h1, cT, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc cT σ y' * cT σ x * J' * (x * y') = cT σ y' * (cT σ x * J' * x) * y' := by simp only [Matrix.mul_assoc]
      _ = (cT σ y' * cT σ y) * J' * (y * y') := by rw [hx, ← hy]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [e, h1, Matrix.one_mul, Matrix.mul_one]
  · rw [hu.unit_spec, Matrix.mul_assoc, h2, Matrix.mul_one]

end Algebra

variable {D : D7}

theorem exists_finE (V : HSp D) (g : GL (Fin V.rank) (EAf D)) (hg : g ∈ UA D.sp.cm V.gram) :
    ∃ k ∈ GfC V, finE V k = g := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
  have e := congrArg Subtype.val hb
  have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
  refine Eq.trans ?_ (e2.symm.trans e)
  exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2

theorem mA_mul (X Y Z : HSp D) (f : X.V →ₗ[D.host.E] Y.V) (g : Y.V →ₗ[D.host.E] Z.V) :
    mA Z Y g * mA Y X f = mA Z X (g.comp f) := by
  rw [mA, mA, mA, ← Matrix.map_mul, frameMat, frameMat, frameMat, LinearMap.toMatrix_comp X.frame Y.frame Z.frame]

theorem mA_id (X : HSp D) : mA X X LinearMap.id = 1 := by
  rw [mA, frameMat, LinearMap.toMatrix_id, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem vA_frame (X : HSp D) (i : Fin X.rank) : vA X (X.frame i) = Pi.single i 1 := by
  funext j
  have : Formalism.L2.Herm.crd X (X.frame i) j = X.frame.repr (X.frame i) j := rfl
  rw [vA, this, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, RingHom.map_one]
  · rw [if_neg h, if_neg (Ne.symm h), RingHom.map_zero]

theorem gram_mA (Y Y' : HSp D) (f : Y.V →ₗ[D.host.E] Y'.V) (hf : HSpace.IsIsomEmb Y Y' f) :
    HMul.hMul (HMul.hMul (cT (cjA D) (mA Y' Y f)) (Y'.gram.map (inc D))) (mA Y' Y f) = Y.gram.map (inc D) := by
  refine gram_of_form _ _ _ _ fun i j => ?_
  rw [← vA_frame, ← vA_frame, mA_mulVec_vA, mA_mulVec_vA, ← hA_eq, hA_vA, HSpace.hD, hf]
  rfl

theorem correction_of_transport : ∀ D : D7, TransportSt D → CorrectionSt D := by
  intro D hT Y Y' io hio Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  have hr : Y.rank = Y'.rank := by rw [← Y.rank_eq, ← Y'.rank_eq, io.finrank_eq]
  obtain ⟨⟨x, hx⟩, -⟩ := hT Y Y' hr Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  obtain ⟨g, hg, hgx⟩ := exists_unitary (cjA D) (Y'.gram.map (inc D)) (Y.gram.map (inc D)) x
    (mA Y' Y io.toLinearMap) (mA Y Y' io.symm.toLinearMap)
    (by rw [mA_mul, LinearEquiv.comp_symm, mA_id]) (by rw [mA_mul, LinearEquiv.symm_comp, mA_id]) hx.1.1.2
    (gram_of_form _ _ _ _ fun i j => (hx.1.2 _ _).trans (hform_single _ _ i j)) (gram_mA Y Y' _ hio)
  obtain ⟨k, hk, e⟩ := exists_finE Y' g hg
  refine ⟨k, hk, ?_⟩
  rw [e, hgx]
  exact hx

end GlobalTheory.AdIsomCorrection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetPositivePartKroneckerBlockUnitaryOrthonormalStatement
section
open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detPositivePartKronecker_blockUnitary_orthonormal : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT → GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) = detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  first | exact @GlobalTheory.PlusDetONB.detPlus_onb | exact GlobalTheory.PlusDetONB.detPlus_onb | (intros; apply GlobalTheory.PlusDetONB.detPlus_onb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominatorSelfDualLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_selfDual_level : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.LevelDenom.exists_denom_congLev | exact GlobalTheory.LevelDenom.exists_denom_congLev | (intros; apply GlobalTheory.LevelDenom.exists_denom_congLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteUnitary_selfDualFrame_to_baseLatticeFrame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  first | exact @GlobalTheory.SelfDualFrameConj.frame_conj | exact GlobalTheory.SelfDualFrameConj.frame_conj | (intros; apply GlobalTheory.SelfDualFrameConj.frame_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  first | exact @GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | exact GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | (intros; apply GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_frameChange_same_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  first | exact @GlobalTheory.FrameChange.ptF_frame_change | exact GlobalTheory.FrameChange.ptF_frame_change | (intros; apply GlobalTheory.FrameChange.ptF_frame_change <;> assumption)
end

