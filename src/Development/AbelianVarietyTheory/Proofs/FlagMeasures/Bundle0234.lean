import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentAddIsotropicToAnisotropic
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def eichG (x v : V) (c : E) (w : V) : V :=
  w + H.h w v • x - H.h w x • v + (c * H.h w x) • x

def eichGL (x v : V) (c : E) : V →ₗ[E] V where
  toFun := eichG H x v c
  map_add' y y' := by
    simp only [eichG, H.h_add_left, add_smul, mul_add]; abel
  map_smul' a y := by
    simp only [eichG, H.h_smul_left, RingHom.id_apply]; module

lemma eichG_hL (x v : V) (c : E) (y w : V) : H.h (eichG H x v c y) w =
    H.h y w + H.h y v * H.h x w - H.h y x * H.h v w + c * H.h y x * H.h x w := by
  simp only [eichG, H.h_add_left, h_sub_left, H.h_smul_left]

lemma eichG_hR (x v : V) (c : E) (w y : V) : H.h w (eichG H x v c y) =
    H.h w y + M.L.cj (H.h y v) * H.h w x - M.L.cj (H.h y x) * H.h w v +
      M.L.cj c * M.L.cj (H.h y x) * H.h w x := by
  simp only [eichG, h_add_right, h_sub_right, h_smul_right, map_mul]

variable {H}

lemma eichG_isom {x v : V} {c : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + M.L.cj c + H.h v v = 0) (y y' : V) :
    H.h (eichG H x v c y) (eichG H x v c y') = H.h y y' := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h x y' = M.L.cj (H.h y' x) := h_right H x y'
  have e2 : H.h v y' = M.L.cj (H.h y' v) := h_right H v y'
  simp only [eichG_hL, eichG_hR]
  rw [hxx, hxv, hvx, e1, e2]
  linear_combination (H.h y x * M.L.cj (H.h y' x)) * hc

lemma eichG_inv {x v : V} {c c' : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + c' + H.h v v = 0) (w : V) :
    eichG H x v c (eichG H (-x) v c' w) = w := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h (eichG H (-x) v c' w) v = H.h w v + H.h w x * H.h v v := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxv]; ring
  have e2 : H.h (eichG H (-x) v c' w) x = H.h w x := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxx, hvx]; ring
  have key : eichG H x v c (eichG H (-x) v c' w) - w = ((c + c' + H.h v v) * H.h w x) • x := by
    unfold eichG at e1 e2 ⊢
    rw [e1, e2, h_neg_right]
    module
  rw [hc, zero_mul, zero_smul, sub_eq_zero] at key
  exact key

lemma smul_memO {Λ : Submodule M.L.O V} {α : E} (hα : α ∈ M.L.O) {v : V} (hv : v ∈ Λ) : α • v ∈ Λ :=
  Λ.smul_mem ⟨α, hα⟩ hv

lemma span_h_left {s : Set V} {u : V} (hs : ∀ g ∈ s, H.h g u ∈ M.L.O) :
    ∀ g ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [H.h_add_left]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h ((α : E) • a) u ∈ M.L.O
    rw [H.h_smul_left]; exact M.L.O.mul_mem α.2 ha

lemma span_h_right {s : Set V} {g : V} (hs : ∀ u ∈ s, H.h g u ∈ M.L.O) :
    ∀ u ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact hs u hu
  | zero => rw [h_zero_right]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [h_add_right]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h g ((α : E) • a) ∈ M.L.O
    rw [h_smul_right]; exact M.L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem M.L α.2) ha

lemma eichG_maps {Λ : Submodule M.L.O V} {x v : V} {c : E} (hc : c ∈ M.L.O) (hxL : x ∈ Λ) (hvL : v ∈ Λ)
    (hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O) (hgv : ∀ g ∈ Λ, H.h g v ∈ M.L.O) :
    ∀ w ∈ Λ, eichG H x v c w ∈ Λ := by
  intro w hw
  unfold eichG
  refine Λ.add_mem (Λ.sub_mem (Λ.add_mem hw (smul_memO (hgv w hw) hxL)) (smul_memO (hgx w hw) hvL))
    (smul_memO (M.L.O.mul_mem hc (hgx w hw)) hxL)

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

lemma e_mem_X (a : Fin r) : Fr.f a.castSucc ∈ H.X Fr.f := Submodule.subset_span ⟨a, rfl⟩

lemma spanO_le_X {x : V} (hx : x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc)) :
    x ∈ H.X Fr.f := by
  induction hx using Submodule.span_induction with
  | mem u hu => exact Submodule.subset_span hu
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul α a _ ha => exact Submodule.smul_mem _ (α : E) ha

lemma e_mem_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) : Fr.f a.castSucc ∈ Fr.LamStd L := by
  refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, by simp⟩⟩
  · rw [Fr.h_es]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [FrameD.e, Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))]; exact M.L.O.zero_mem
  · have h2 : ∀ b, H.h (Fr.f a.castSucc) (Fr.e b) = 0 := fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
    simp only [FrameD.prF, Fr.h_es, h2, zero_smul, Finset.sum_const_zero, sub_zero, ite_smul, one_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [FrameD.e]

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

theorem zstep : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L →
    ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h (Fr.f (Fin.last r)) (y : V) = 1 →
    (∀ a, H.h (y : V) (Fr.es a) = 0) →
    ∀ x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc),
    ∃ n ∈ Fr.N, n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) + x ∧ (∀ w ∈ H.X Fr.f, n w = w) ∧
      img n (Fr.LamStd L) = Fr.LamStd L := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr L hL y hyL hzy hyes x hx
  letI := hOK.loc
  haveI := hOK.char0

  have hyX : ∀ w ∈ H.X Fr.f, H.h w (y : V) = 0 := fun w hw => by rw [h_right, y.2 w hw, map_zero]
  have hxX : x ∈ H.X Fr.f := spanO_le_X Fr hx
  have hxx : H.h x x = 0 := X_iso Fr x hxX x hxX
  have hxy : H.h x y = 0 := hyX x hxX
  have hnx : H.h (-x) (-x) = 0 := by rw [h_neg_left, h_neg_right, neg_neg, hxx]
  have hny : H.h (-x) y = 0 := by rw [h_neg_left, hxy, neg_zero]

  have hyy : H.h (y : V) y ∈ M.L.O := (hL.2.1 y).1 hyL y hyL
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed M.L hyy (H.h_herm _ _).symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨c, hcO, hc⟩ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).1 (-t)
  have hc1 : c + M.L.cj c + H.h (y : V) y = 0 := by
    rw [hc, ht, ← map_add]
    simp
  have hc2 : M.L.cj c + c + H.h (y : V) y = 0 := by rw [← hc1]; ring
  have hcjO : M.L.cj c ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hcO

  let n : V ≃ₗ[E] V := LinearEquiv.ofLinear (ZStep.eichGL H x y c) (ZStep.eichGL H (-x) y (M.L.cj c))
    (LinearMap.ext fun w => ZStep.eichG_inv hxx hxy hc1 w)
    (LinearMap.ext fun w => by
      have := ZStep.eichG_inv (c := M.L.cj c) (c' := c) hnx hny hc2 w
      rw [neg_neg] at this
      exact this)
  have hn : ∀ w, n w = ZStep.eichG H x y c w := fun w => rfl

  set Λ := Fr.LamStd L with hΛ
  have heL : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => e_mem_LamStd Fr L a
  have hxL : x ∈ Λ := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, rfl⟩
    exact heL a
  have hyLam : (y : V) ∈ Λ := by
    refine Submodule.subset_span ⟨fun a => by rw [hyes a]; exact M.L.O.zero_mem,
      fun a => by rw [show H.h (y : V) (Fr.e a) = 0 from y.2 _ (e_mem_X Fr a)]; exact M.L.O.zero_mem, ⟨y, ?_, hyL⟩⟩
    have h2 : ∀ a, H.h (y : V) (Fr.e a) = 0 := fun a => y.2 _ (e_mem_X Fr a)
    simp [FrameD.prF, hyes, h2]

  have hgen : ∀ g ∈ {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L},
      H.h g y ∈ M.L.O ∧ H.h g x ∈ M.L.O := by
    rintro g ⟨hges, hge, w, hw, hwL⟩
    refine ⟨?_, ?_⟩
    · have hpr : H.h (Fr.prF g) y = H.h g y := by
        have h1 : ∀ a, H.h (Fr.es a) (y : V) = 0 := fun a => by rw [h_right, hyes a, map_zero]
        have h2 : ∀ a, H.h (Fr.e a) (y : V) = 0 := fun a => hyX _ (e_mem_X Fr a)
        simp only [FrameD.prF, h_sub_left]
        rw [show H.h (∑ a, H.h g (Fr.es a) • Fr.e a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.es a) • Fr.e a) from rfl,
          show H.h (∑ a, H.h g (Fr.e a) • Fr.es a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.e a) • Fr.es a) from rfl,
          map_sum, map_sum]
        simp [UnipOnto.lf, H.h_smul_left, h1, h2]
      rw [← hpr, ← hw]
      exact (hL.2.1 w).1 hwL y hyL
    · refine span_h_right (s := Set.range fun a : Fin r => Fr.f a.castSucc) ?_ x hx
      rintro _ ⟨a, rfl⟩
      exact hge a
  have hgy : ∀ g ∈ Λ, H.h g y ∈ M.L.O := span_h_left fun g hg => (hgen g hg).1
  have hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O := span_h_left fun g hg => (hgen g hg).2
  have hgnx : ∀ g ∈ Λ, H.h g (-x) ∈ M.L.O := fun g hg => by
    rw [h_neg_right]; exact M.L.O.neg_mem (hgx g hg)
  have hmap := eichG_maps hcO hxL hyLam hgx hgy
  have hmap' := eichG_maps hcjO (Λ.neg_mem hxL) hyLam hgnx hgy
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · rw [N_eq]
    show n ∈ NU H Fr.f
    refine ⟨fun w w' => eichG_isom hxx hxy hc1 w w', fun a => ?_, fun v hv => ?_⟩
    · have h1 : H.h (Fr.f a.castSucc) y = 0 := hyX _ (e_mem_X Fr a)
      have h2 : H.h (Fr.f a.castSucc) x = 0 := X_iso Fr _ (e_mem_X Fr a) x hxX
      rw [hn]
      simp only [eichG, h1, h2, zero_smul, mul_zero, add_zero, sub_zero, sub_self]
      exact Submodule.zero_mem _
    · have h2 : H.h v x = 0 := hv x hxX
      rw [hn]
      have : eichG H x y c v - v = H.h v y • x := by simp [eichG, h2]
      rw [this]
      exact Submodule.smul_mem _ _ hxX
  · rw [hn]
    have hzx : H.h (Fr.f (Fin.last r)) x = 0 := z_X Fr x hxX
    simp [eichG, hzy, hzx]
  · intro w hw
    rw [hn]
    have h1 : H.h w y = 0 := hyX w hw
    have h2 : H.h w x = 0 := X_iso Fr w hw x hxX
    simp [eichG, h1, h2]
  · apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hmap w hw
    · intro w hw
      exact ⟨eichG H (-x) y (M.L.cj c) w, hmap' w hw, eichG_inv hxx hxy hc1 w⟩

end GlobalTheory.LocOver.ZStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOntoStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ Fr : FrameD H r, Fr.T ≠ 0 → (∀ n, n ∈ Fr.N ↔ n ∈ NU H Fr.f) ∧ (∀ n ∈ Fr.N, Tri E Fr.f fun b => n (Fr.f b)) ∧ ∀ g : Fin (r + 1) → V, Tri E Fr.f g → ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  first | exact @GlobalTheory.LocOver.UnipOnto.unipotent_onto | exact GlobalTheory.LocOver.UnipOnto.unipotent_onto | (intros; apply GlobalTheory.LocOver.UnipOnto.unipotent_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeToStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  first | exact @GlobalTheory.HL.PrimeToOrbit.main | exact GlobalTheory.HL.PrimeToOrbit.main | (intros; apply GlobalTheory.HL.PrimeToOrbit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDatum_of_term_read_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → (∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f) ∧ ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → H.Lset t.abelian₂ P.A.f = H.Lset t'.abelian₂ P.A.f → H.Lset t.abelian₂ P.B.f = H.Lset t'.abelian₂ P.B.f → (∀ g, M.split = some g → H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = H.iotaGraph g ⟨t'.abelian₂, P.A.f, P.B.f, t'.T, t'.T'⟩) → d = d' := by
  first | exact @GlobalTheory.LocOver.TermLat.datum_of_lattice | exact GlobalTheory.LocOver.TermLat.datum_of_lattice | (intros; apply GlobalTheory.LocOver.TermLat.datum_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetSecondTypeFamilyAmpSqLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  first | exact @GlobalTheory.HL.FamilyBound.family_bound | exact GlobalTheory.HL.FamilyBound.family_bound | (intros; apply GlobalTheory.HL.FamilyBound.family_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBoundStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_gap_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g₀ : ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) → 2 * (n : ℝ) < g₀ → ∀ F : Matrix (Fin n) (Fin n) ℂ → (H →ₗ[ℂ] H), (∀ g ∈ UJset ε, ∀ x ∈ (kSpan ε E u).map V.subtype, F g x ∈ (kSpan ε E u).map V.subtype ∧ ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, F (k₁ * g * k₂) x = σ k₁ (F g (σ k₂ x))) → (∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, SmoothOnG ε (fun g => ⟪y, F g x⟫_ℂ)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ⟪y, F z (at1 G a b : V)⟫_ℂ) (umat g) = 0) → (∀ x ∈ (kSpan ε E u).map V.subtype, F 1 x = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, Eword ε w (fun g => ⟪y, F g x⟫_ℂ) 1 = 0 := by
  first | exact @GlobalTheory.Jet.Germ.germ_jet_zero | exact GlobalTheory.Jet.Germ.germ_jet_zero | (intros; apply GlobalTheory.Jet.Germ.germ_jet_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselFubiniIntegrandProd
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SgInf

theorem prod_integrand_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hF := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v hv
  obtain ⟨hz, hT, hπ, hHaarS, _⟩ := hSide
  have : SigmaFinite μS := hHaarS.1
  have : SigmaFinite μG := hStd.2.2.2.2.1.1
  obtain ⟨-, -, hPiB, hPiC, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hS : IsClosedSub k r (Sset k r z) := (closedSub_groups k r z hz hT).2.2.2.1

  set T : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ Sset k r z} with hTdef
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hTm : MeasurableSet T := (hS.2.1.preimage hof).measurableSet
  have haeT : ∀ᵐ x ∂μS, x ∈ T := ae_iff.2 hHaarS.2.2.1

  have hinv : ContinuousOn (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T := by
    intro x hx
    have hg : (Matrix.of x : Mat k r)ᴴ * Hpk k r * (Matrix.of x : Mat k r) = Hpk k r := hS.1 hx
    have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
    have hdet : IsUnit (Matrix.of x : Mat k r).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have h1 := congrArg Matrix.det hg
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
      exact hH.ne_zero h1.symm
    have hc : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact ((continuousAt_matrix_inv _ hc).comp hof.continuousAt).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T (Sset k r z) :=
    fun x hx => hS.2.2.2.2 _ hx
  have hgc : ContinuousOn
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) T :=
    ((hPiC.comp hinv hmaps).clm_apply continuousOn_const).inner continuousOn_const
  have hgm : AEStronglyMeasurable
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) μS := by
    have h1 := hgc.aestronglyMeasurable (μ := μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem haeT] at h1

  have hbd : ∀ x ∈ T,
      ‖⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖ξ‖ := by
    intro x hx
    have h1 := (hPiB _ (hmaps hx)).1
    calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * ‖ξ‖ := by
        gcongr
        calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹‖ * ‖ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖ξ‖ := by gcongr
          _ = ‖ξ‖ := one_mul _
  have haeP : ∀ᵐ p ∂(μG.prod μS), p.2 ∈ T := by
    rw [ae_iff]
    have h1 : {p : Mt k r × Mt k r | ¬ p.2 ∈ T} = Set.univ ×ˢ {x | ¬ x ∈ T} := by
      ext p; simp
    rw [h1, Measure.prod_prod, ae_iff.1 haeT, mul_zero]
  refine hF.mul_bdd (c := ‖ξ‖ * ‖ξ‖)
    (hgm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd) ?_
  filter_upwards [haeP] with p hp
  exact hbd p.2 hp

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitary
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.QuotUniq

theorem lintegral_le {k r : ℕ} {R : Set (Mat k r)} {μG μR ν ν' : Measure (Mt k r)}
    (hR : IsClosedSub k r R) (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (hU : IsUnimod R μR)
    (hν : IsQuotMeas μG μR ν) (hν' : IsQuotMeas μG μR ν') (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) :
    ∫⁻ x, F x ∂ν ≤ ∫⁻ x, F x ∂ν' := by
  obtain ⟨-, -, φ, hφ, h⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν
  obtain ⟨h1, -, -⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'
  have h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r := h1
  have hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν' := hν'
  have hTm := (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  rw [h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]
  refine lintegral_mono_ae ?_
  filter_upwards [h1'] with x hx
  have hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x :=
    hTm.comp (measurable_id.prodMk measurable_const)
  have h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR =
      ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hFi _ hs x hx]
  rw [h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]
  exact mul_le_of_le_one_left zero_le (hφ.2 x hx)

theorem quot_uniq : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  intro k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi
  classical
  borelize V
  set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS
  have hSm : MeasurableSet S := GlobalTheory.Amp.CutQuot.measurable_G k r
  have hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S := hF
  set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'
  have hF'm : Measurable F' := hFc.measurable_piecewise continuousOn_const hSm
  have hsep : TopologicalSpace.IsSeparable (Set.range F') := by
    have h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S) :=
      hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)
    refine (h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩
    · exact Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)
  have hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x := by
    intro ρ hρ x hx
    have hx' : lmulM ρ x ∈ S := (GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]
    exact hFi ρ hρ _ hx
  have hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r)) :=
    hF'm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F' :=
    (@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance)
      _ _ _ _).2 ⟨comap_measurable F', hsep⟩
  have htrim : ν.trim hm = ν'.trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    have hAm : MeasurableSet A := hm A hA
    obtain ⟨B, -, rfl⟩ := hA
    have hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r →
        (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x := by
      intro ρ hρ x hx
      simp only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]
    rw [← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]
    exact le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi)
      (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)
  have hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ →
      (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F' := by
    intro ν₀ h
    have h1 : ∀ᵐ x ∂ν₀, x ∈ S := (GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1
    filter_upwards [h1] with x hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]
  rw [integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν),
    integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)
  · exact integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)

end GlobalTheory.SnMass.QuotUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometryStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_localTermMove_of_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_move_of_unitary | exact GlobalTheory.LocOver.isTerm_move_of_unitary | (intros; apply GlobalTheory.LocOver.isTerm_move_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermUnitaryMoveLocalTerm
section
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocOver

theorem isTerm_unitary_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (r : ℕ) (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht

end GlobalTheory.LocOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExactStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIndices_column_row_levels_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  first | exact @GlobalTheory.idxColLoc_idxRowLoc_exact | exact GlobalTheory.idxColLoc_idxRowLoc_exact | (intros; apply GlobalTheory.idxColLoc_idxRowLoc_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCongruenceLevelIffOrthEmbeddingStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruence_level_iff_orthEmbedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf → (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧ ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  first | exact @GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | exact GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb | (intros; apply GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb <;> assumption)
end

