import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem sup_span_add {P : Submodule D.host.E (VS D).V} {x d : (VS D).V} (hd : d ∈ P) :
    P ⊔ Submodule.span D.host.E {x + d} = P ⊔ Submodule.span D.host.E {x} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left hd)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have h2 : x + d ∈ P ⊔ Submodule.span D.host.E {x + d} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (x + d))
    have h3 : d ∈ P ⊔ Submodule.span D.host.E {x + d} := Submodule.mem_sup_left hd
    have h1 := Submodule.sub_mem _ h2 h3
    simpa using h1

variable {T : D.host.E}

theorem xflag_succ (A : LFlag (VS D) D.R.rS T) (j : ℕ) (hj : j < D.R.rS) :
    Xflag A (j + 1) = Xflag A j ⊔ Submodule.span D.host.E {A.fl.e ⟨j, hj⟩} := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j + 1}) = Submodule.span _ (A.fl.e '' {i | i.1 < j}) ⊔ _
  rw [← Set.image_singleton, ← Submodule.span_union, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem xflag_ge (A : LFlag (VS D) D.R.rS T) (j : ℕ) (hj : D.R.rS ≤ j) : Xflag A j = Xflag A D.R.rS := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j}) = Submodule.span _ (A.fl.e '' {i | i.1 < D.R.rS})
  congr 2
  ext i
  simp only [Set.mem_setOf_eq]
  omega

theorem frame_castSucc (A : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last (A : LFlag (VS D) D.R.rS T) : frame A (Fin.last _) = A.fl.z := by
  simp [frame, FlagG.fvec]

theorem adapt_xflag {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) (j : ℕ) :
    (Xflag A j).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag B j := by
  induction j with
  | zero => rw [xflag_zero, xflag_zero, Submodule.map_bot]
  | succ j ih =>
    by_cases hj : j < D.R.rS
    · rw [xflag_succ A j hj, xflag_succ B j hj, Submodule.map_sup, ih, Submodule.map_span, Set.image_singleton]
      have hd := h.2 (Fin.castSucc ⟨j, hj⟩)
      rw [frame_castSucc, frame_castSucc, Fin.coe_castSucc] at hd
      have e : (a : (VS D).V →ₗ[D.host.E] (VS D).V) (A.fl.e ⟨j, hj⟩) = B.fl.e ⟨j, hj⟩ + (a (A.fl.e ⟨j, hj⟩) - B.fl.e ⟨j, hj⟩) := by
        simp
      rw [e, sup_span_add hd]
    · rw [xflag_ge A (j + 1) (by omega), xflag_ge B (j + 1) (by omega), ← xflag_ge A j (by omega),
        ← xflag_ge B j (by omega), ih]

theorem adapt_xsp {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (Xsp A).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := by
  rw [xsp_eq, xsp_eq, adapt_xflag h]

theorem orth_map_isom {a : GV D} (ha : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') :
    (orth (VS D) U).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) U' := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_orth_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ x' hx'
    rw [← hU] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    simp only [LinearEquiv.coe_coe]
    rw [ha]; exact hv x hx
  · intro hw
    refine ⟨a.symm w, fun x hx => ?_, by simp⟩
    have := hw (a x) (hU ▸ Submodule.mem_map_of_mem hx)
    have e : (VS D).hT (a x) (a (a.symm w)) = (VS D).hT x (a.symm w) := ha _ _
    simp only [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem adapt_orth {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (orth (VS D) (Xsp A)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp B) :=
  orth_map_isom h.1 (adapt_xsp h)

theorem mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {x : (VS D).V} (hx : x ∈ U) : a x ∈ U' := by
  rw [← hU]; exact Submodule.mem_map_of_mem hx

theorem symm_mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {y : (VS D).V} (hy : y ∈ U') : a.symm y ∈ U := by
  rw [← hU] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

theorem adapt_mul {A B C : LFlag (VS D) D.R.rS T} {a b : GV D} (ha : Adapt a A B) (hb : Adapt b B C) :
    Adapt (b * a) A C := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hb.1 ha.1, fun k => ?_⟩
  have e : (b * a) (frame A k) - frame C k = b (a (frame A k) - frame B k) + (b (frame B k) - frame C k) := by
    rw [le_mul_app, map_sub]; abel
  rw [e]
  exact add_mem (mem_of_map_eq (adapt_xflag hb _) (ha.2 k)) (hb.2 k)

theorem adapt_inv {A B : LFlag (VS D) D.R.rS T} {a : GV D} (ha : Adapt a A B) : Adapt a⁻¹ B A := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1, fun k => ?_⟩
  have e : a⁻¹ (frame B k) - frame A k = -(a.symm (a (frame A k) - frame B k)) := by
    rw [le_inv_app, map_sub]; simp
  rw [e]
  exact neg_mem (symm_mem_of_map_eq (adapt_xflag ha _) (ha.2 k))

theorem z_mem_orth (A : LFlag (VS D) D.R.rS T) : A.fl.z ∈ orth (VS D) (Xsp A) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact A.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem adapt_nrat {A : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat A) : Adapt n A A := by
  refine ⟨hn.1, fun k => ?_⟩
  induction k using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, ← xsp_eq]
    exact hn.2.2 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    apply hn.2.1 i.1
    show A.fl.e i ∈ Submodule.span _ (A.fl.e '' {k | k.1 < i.1 + 1})
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

theorem frameAdaptedIsometry_of_fixing_both_frames {T' : D.host.E} {A : LFlag (VS D) D.R.rS T} {A' : LFlag (VS D) D.R.rS T'} {h : GV D}
    (hh : h ∈ H0 A A') : Adapt h A A ∧ Adapt h A' A' :=
  ⟨⟨hh.1, fun k => by rw [hh.2.1 k, sub_self]; exact zero_mem _⟩,
   ⟨hh.1, fun k => by rw [hh.2.2 k, sub_self]; exact zero_mem _⟩⟩

theorem adapt_mapLF {A : LFlag (VS D) D.R.rS T} {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Adapt γ A (mapLF γ A) := by
  refine ⟨hγ, fun k => ?_⟩
  have : frame (mapLF γ A) k = γ (frame A k) := by
    simp only [mapLF, dif_pos hγ, frame]
    rw [fvec_mapFlag]
  rw [this, sub_self]; exact zero_mem _

theorem nrat_conj {A B : LFlag (VS D) D.R.rS T} {a n : GV D} (ha : Adapt a A B) (hn : n ∈ NRat A) :
    a * n * a⁻¹ ∈ NRat B := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ha.1 hn.1)
    ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1), fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xflag ha j) (hn.2.1 j _ (symm_mem_of_map_eq (adapt_xflag ha _) hx))
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ (symm_mem_of_map_eq (adapt_orth ha) hx))

theorem nrat_eq_nlam (A : LFlag (VS D) D.R.rS T) : NRat A = NLam ⊤ A := by
  ext n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_top, LinearMap.range_eq_top]
    exact n.surjective
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

def NRatSub (A : LFlag (VS D) D.R.rS T) : Subgroup (GV D) := NLamSub ⊤ A

theorem mem_nratSub {A : LFlag (VS D) D.R.rS T} {n : GV D} : n ∈ NRatSub A ↔ n ∈ NRat A := by
  rw [nrat_eq_nlam]; rfl

theorem nrat_mul {A : LFlag (VS D) D.R.rS T} {a b : GV D} (ha : a ∈ NRat A) (hb : b ∈ NRat A) : a * b ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).mul_mem (mem_nratSub.2 ha) (mem_nratSub.2 hb))

theorem nrat_inv {A : LFlag (VS D) D.R.rS T} {a : GV D} (ha : a ∈ NRat A) : a⁻¹ ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).inv_mem (mem_nratSub.2 ha))

theorem nrat_one (A : LFlag (VS D) D.R.rS T) : (1 : GV D) ∈ NRat A :=
  mem_nratSub.1 (NRatSub A).one_mem

section Defs

variable {T T' : D.host.E}

def InB (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (lam lam' : LV D) (γ : GV D)
    (b : GV D × GV D) : Prop :=
  b.1 ∈ Aut0 F0 lam ∧ b.2 ∈ Aut0 F0' lam' ∧ KeyEq F0 F0' lam γ (b.1 * γ * b.2⁻¹)

def Corr (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (γ g : GV D) (b : GV D × GV D)
    (h : GV D) : Prop :=
  h ∈ H0 F F' ∧ ∃ n ∈ NRat F0, ∃ n' ∈ NRat F0', b.1 * γ * b.2⁻¹ = n * γ * n' ∧
    h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F ∧ h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F'

end Defs

end GlobalTheory.StabCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesSameGramDifferBySkewSolution
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FrameDiff

theorem dd_zpow_le (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ddS D ^ (-(D.R.rS : ℤ)) := by
  have ha := a.2
  by_cases h0 : ddS D = 0
  · rw [h0, _root_.zero_zpow _ (by omega)]
    exact FractionalIdeal.zero_le _
  · have h1 : (-((D.R.rS : ℤ) - (a : ℕ))) = -(D.R.rS : ℤ) + ((a : ℕ) : ℤ) := by ring
    rw [h1, zpow_add₀ h0, zpow_natCast]
    have h2 : ddS D ^ (a : ℕ) ≤ 1 := by
      unfold ddS
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    calc _ ≤ ddS D ^ (-(D.R.rS : ℤ)) * 1 := by gcongr
      _ = _ := mul_one _

theorem coords_of_mem_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (y : (VS D).V)
    (hy : y ∈ XS D F0) :
    ∃ c : Fin D.R.rS → D.host.E,
      (∀ a, c a ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
      y = ∑ a, c a • F0.e a := by
  unfold XS at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨Pi.single a x, fun a' => ?_, ?_⟩
    · by_cases h : a' = a
      · subst h
        rw [Pi.single_eq_same]
        exact dd_zpow_le D a' hx
      · rw [Pi.single_eq_of_ne h]
        exact FractionalIdeal.zero_mem _
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨c', hc', rfl⟩ := h'
    refine ⟨c + c', fun a => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
    exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) (hc a) (hc' a)
  | smul o y _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    refine ⟨o • c, fun a => ?_, by simp [Finset.smul_sum, smul_assoc]⟩
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _) o (hc a)

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem star_hT (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem gram_eq (F F' : FlagG S r T) (b b' : Fin (r + 1)) :
    S.hT (F.fvec b) (F.fvec b') = S.hT (F'.fvec b) (F'.fvec b') := by
  have hz : ∀ (G : FlagG S r T) a, S.hT G.z (G.e a) = 0 := fun G a => by
    rw [← star_hT, G.z_orth, star_zero]
  induction b using Fin.lastCases <;> induction b' using Fin.lastCases <;>
    simp [FlagG.fvec, F.e_iso, F'.e_iso, F.z_orth, F'.z_orth, F.z_norm, F'.z_norm, hz]

theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem hT_X_eq_zero (F : FlagG S r T) (v : S.V) (hv : ∀ a, S.hT (F.e a) v = 0) (x : S.V) (hx : x ∈ F.X) :
    S.hT x v = 0 := by
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hv a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_mem (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (h : IsLift Λ F) (he : ∀ a, F.fl.e a ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => simpa [FlagG.fvec] using h.1
  | cast a => simpa [FlagG.fvec] using he a

end Gen

theorem mem_perpE_iff (D : D7) (P : LatW D) (w : (D.sp.X 0).V) :
    w ∈ perpE D P ↔ ∀ p ∈ P, (D.sp.X 0).hT p w = 0 := by
  simp [perpE, Submodule.mem_iInf]

theorem frame_diff : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  intro D u u' F0 Λ hst hb hrow P φ Z hφ F₁ h₁ F₂ h₂ hw
  obtain ⟨hW, -, hpos, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hst hb hrow
  obtain ⟨l₁, e₁, z₁, o₁⟩ := h₁
  obtain ⟨l₂, e₂, z₂, o₂⟩ := h₂
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  have hZ₁ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₁ b) = Z a b := fun a b => by rw [← z₁]; rfl
  have hZ₂ : ∀ a b, (hS D).hT (F0.fvec a) (frame F₂ b) = Z a b := fun a b => by rw [← z₂]; rfl
  have hWX : ∀ (w : (D.sp.X 0).V), ∀ x ∈ F0.X, (hS D).hT (D.sp.iXY 0 w) x = 0 := by
    intro w x hx
    rw [← star_hT, hT_X_eq_zero F0 (D.sp.iXY 0 w) (fun a => ?_) x hx, star_zero]
    rw [← star_hT, hb.1, (D.sp.hyp_orthX a w).1, star_zero]
  have hd : ∀ b, frame F₂ b - frame F₁ b ∈ XS D F0 := by
    intro b
    rw [← hrow.2.2]
    refine ⟨Λ.sub_mem (frame_mem Λ F₂ l₂ e₂ b) (frame_mem Λ F₁ l₁ e₁ b), ?_⟩
    set d := frame F₂ b - frame F₁ b with hdd
    have hf : ∀ a, (hS D).hT (F0.fvec a) d = 0 := fun a => by rw [hdd, map_sub, hZ₁, hZ₂, sub_self]
    have hX : ∀ x ∈ F0.X, (hS D).hT x d = 0 :=
      hT_X_eq_zero F0 d (fun a => by simpa [FlagG.fvec] using hf a.castSucc)
    have hz : (hS D).hT F0.z d = 0 := by simpa [FlagG.fvec] using hf (Fin.last _)
    have hmem : d ∈ Wsp D ⊔ Xsp (lf D F0) := by
      rw [hW.1, mem_orth_iff]
      intro y hy
      obtain ⟨x, hx, y', hy', rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      simp [hX x hx, hz]
    obtain ⟨_, ⟨w, rfl⟩, x, hx, hwx⟩ := Submodule.mem_sup.1 hmem
    have hwd : ∀ σ, (hS D).hT (D.sp.iXY 0 σ) d = (D.sp.X 0).hT σ w := fun σ => by
      rw [← hwx, map_add, hiso, hWX σ x hx, add_zero]
    have hwP : w ∈ perpE D P := by
      rw [mem_perpE_iff]
      intro p hp
      have h1 : (hS D).hT (D.sp.iXY 0 p + φ ⟨p, hp⟩) d = 0 := by
        rw [hdd, map_sub, o₁ ⟨p, hp⟩ b, o₂ ⟨p, hp⟩ b, sub_self]
      rw [map_add, LinearMap.add_apply, hX _ (hφ ⟨p, hp⟩).2, add_zero, hwd] at h1
      exact h1
    obtain ⟨w', c₁, c₂⟩ := hw b
    have hww : (D.sp.X 0).hT w w = 0 := by
      rw [← hwd, hdd, map_sub, c₁.2 w hwP, c₂.2 w hwP, sub_self]
    have hw0 : w = 0 := by
      by_contra hne
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have := hpos τ w hne
      rw [hww] at this
      simp at this
    rw [hw0, map_zero, zero_add] at hwx
    rw [← hwx]
    exact hx
  choose c hc hcd using fun b => coords_of_mem_XS D F0 _ (hd b)
  have hfr : ∀ b, frame F₂ b = frame F₁ b + ∑ a, c b a • F0.e a := fun b => by
    rw [← hcd]; abel
  refine ⟨Matrix.of fun a b => c b a, hfr, fun a b => hc b a, ?_⟩
  refine Matrix.ext fun b b' => ?_
  have hg : (hS D).hT (frame F₂ b) (frame F₂ b') = (hS D).hT (frame F₁ b) (frame F₁ b') :=
    gram_eq F₂.fl F₁.fl b b'
  have hY : ∀ a b, (hS D).hT (F0.e a) (frame F₁ b) = Z a.castSucc b := fun a b => by
    simpa [FlagG.fvec] using hZ₁ a.castSucc b
  have hY' : ∀ a b, (hS D).hT (frame F₁ b) (F0.e a) = star (Z a.castSucc b) := fun a b => by
    rw [← hY, star_hT]
  rw [hfr b, hfr b'] at hg
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hY, hY', F0.e_iso, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero,
    starRingEnd_apply] at hg
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.submatrix_apply, id, Matrix.zero_apply]
  have : ∑ a, star (Z a.castSucc b) * c b' a = ∑ a, c b' a * star (Z a.castSucc b) :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [this]
  linear_combination hg

end GlobalTheory.LoopC.FrameDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivityStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), (∀ a, lA k r z (s * x * κ) a = lA k r z x a) ∧ Sg k r z (s * x * κ) = Sg k r z x) ∧ (∀ (a : Fin r → ℝ), (∀ b, 0 < a b) → ∀ m ∈ UH (Hb k), ∀ b : Fin r, lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹) ∧ (∀ x, 1 ≤ Sg k r z x ∧ (∀ a, 0 ≤ lA k r z x a ∧ lA k r z x a ≤ Sg k r z x) ∧ (Sg k r z x = 1 ∨ ∃ a, Sg k r z x = lA k r z x a)) := by
  first | exact @GlobalTheory.Amp.LInv.lengths_basic | exact GlobalTheory.Amp.LInv.lengths_basic | (intros; apply GlobalTheory.Amp.LInv.lengths_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureFundamentalDomainLtOfDeepPointBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_fundamentalDomain_lt_of_deepPoint_bound : GlobalTheory.FlagMeas.AbsoluteVolume → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → B.I.muA B.μf B.fund < ⊤ ∧ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal * (B.I.muA B.μf B.fund).toReal ≤ Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) := by
  first | exact @GlobalTheory.DeepArith.deep_mul_volume_le | exact GlobalTheory.DeepArith.deep_mul_volume_le | (intros; apply GlobalTheory.DeepArith.deep_mul_volume_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatements
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamNG

theorem ampQ_id {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ id L = L.ampNG := by
  funext d
  unfold ampQ PN.LocalNG.ampNG
  simp only [id]

theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ} {γ : PN.Pts D.host.E D.R.rS}
    (h : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ) : HasPt Y u u' (Y.tO u u').ngSet γ := by
  obtain ⟨-, -, t, ht, hv, -, hp, -⟩ := h
  exact ⟨t, ht, hv, hp⟩

theorem leaves_of_fam : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧
    (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  intro hF
  refine ⟨fun hG => ?_, fun hW => ?_, fun hG4 => ?_, fun hE => ?_⟩
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hG Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S Fm hT => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ
      (hasPt_of_isPt hγ) Fm hT
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hW Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
      hbk νL νB ng γ hγ S Fm hT hRel hTerm hG5 => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q
      i0 i0' νq Irat Ire hbk _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT hRel hTerm hG5
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨CSt, hCSt, a2, b2, h2⟩ := hG4 Cg cb Cw cT CT C0
    refine ⟨CSt, hCSt, max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0'
      νq Irat Ire hbk ν hν => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0
      ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hν
    refine ⟨s, hs1, hs2, hs3, fun γ hγ S Fm hT x _ => ?_⟩
    have h := hs4 _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT x.1 x.2
    rw [ampQ_id] at h
    exact h
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hE Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ (hasPt_of_isPt hγ)

end GlobalTheory.SnFamNG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower
section
namespace GlobalTheory.HTThetaLeaf

theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompactStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  first | exact @GlobalTheory.isPureFin_continuous_hasCompactSupport | exact GlobalTheory.isPureFin_continuous_hasCompactSupport | (intros; apply GlobalTheory.isPureFin_continuous_hasCompactSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelicStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightConvolution_operator_ae_eq_integral_adelic : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ConvKernel.rconv_eq_integral | exact GlobalTheory.ConvKernel.rconv_eq_integral | (intros; apply GlobalTheory.ConvKernel.rconv_eq_integral <;> assumption)
end

