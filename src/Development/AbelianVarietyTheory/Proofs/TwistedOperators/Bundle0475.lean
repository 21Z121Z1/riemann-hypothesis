import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndex
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHomIdx

open GlobalTheory.FinWeilO

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X) (M : X →+ Y)
    (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    A.relIndex (A.map φ) = (A.map M).relIndex ((A.map M).map m) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := A.map M) M (A.map φ), ← AddSubgroup.inf_relIndex_right A,
    ← AddSubgroup.inf_relIndex_right ((A.map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨a, ha, hax⟩, hx⟩
  refine ⟨?_, hx⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : P (a - φ y) = 0 := hK _ (by rw [map_sub, hax, sub_self])
  have h2 : P (φ y) = P a := by rw [map_sub, sub_eq_zero] at h1; exact h1.symm
  have h3 : φ y = (y - P y) + P a := by rw [← hφ y hy, h2]; abel
  rw [h3]
  exact add_mem (sub_mem hy (hPA y hy)) (hPA a ha)

end GlobalTheory.InertHomIdx

open GlobalTheory.FinWeilO in

theorem GlobalTheory.InertHomIdx.idx_latF_moved : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : Gv T v, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v g))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1)) := by
  intro D S T v w h hi g
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hε : IsPlaceIdem D v ε := hns.1
  have hη : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hk : GlobalTheory.WeilParts.SuppPl ε T (embV T v g) := by
    rw [GlobalTheory.PlaceDatum.placeIdem_eq hε hη]
    exact GlobalTheory.PlaceTensor.suppPl_emb T v g
  have hg : GlobalTheory.WeilParts.SuppPl ε S (1 : GA D S) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have hmat : (mt T (embV T v g)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v g)
    rw [proj_emb_self] at e
    exact e
  refine GlobalTheory.InertHomIdx.relIndex_map_of_proj (latF S T (frameLat S) (frameLat T)).toAddSubgroup
    (rhoF S T (1, embV T v g)).toAddMonoidHom (mulF S T (algebraMap (AF D.host.F) (AE D) ε)).toAddMonoidHom
    (GlobalTheory.InertHomIdx.matW S T w) (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1) ?_ ?_ ?_ ?_
  · intro x
    show (actO S T 1 (embV T v g) x).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 * (x : WO S T).map (GlobalTheory.InertHomIdx.compW D w)
    rw [actO, inv_one, mt_one, Matrix.mul_one, Matrix.map_mul, hmat]
  · intro x hx
    refine XF.ext (Matrix.ext fun i j => ?_)
    have h0 : GlobalTheory.InertHomIdx.compW D w ((x : WO S T) i j) = 0 := congrFun (congrFun hx i) j
    show algebraMap (AF D.host.F) (AE D) ε * (x : WO S T) i j = 0
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hp, zero_mul, RingHom.map_zero]
    · rw [RingHom.map_mul, finPart_of_isPrimeIdem hp, singleAt_mul, RingHom.map_zero]
      have h1 : compAt D.host.F w (finPart D ((x : WO S T) i j)) = 0 := h0
      rw [h1, mul_zero, ← singleAt_zero]
  · intro a ha
    exact GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha)
  · intro a _
    refine XF.ext ?_
    have := hoff (a : WO S T)
    rw [sub_smul, sub_smul, one_smul, one_smul] at this
    exact this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.SelfDualGlue

variable {D : D7} {u : D.what₂.Word} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V}

theorem vA_flat (x : X.V) (a : D.host.E) : vA Y (ι x + a • z) = mA Y X ι *ᵥ vA X x + inc D a • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem inc_hD_flat (h : IsLine Y X ι z u) (x x' : X.V) (a a' : D.host.E) :
    inc D (Y.hD (ι x + a • z) (ι x' + a' • z)) =
      hA X (vA X x) (vA X x') - inc D a * cjA D (inc D a') * inc D (Tu D u) := by
  rw [← hA_vA, vA_flat, vA_flat]
  exact hA_flat h _ _ _ _

theorem mem_glueLat_iff {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E,
      y = ι (x + (a : D.host.E) • x₀) + ((a : D.host.E) * (Tu D u)⁻¹) • z := by
  rw [mem_glueLat]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun a => ?_
  rw [map_add, map_smul, smul_add, smul_smul]
  constructor <;> rintro rfl <;> abel

theorem coords_of_mem (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ x : X.V} {a : D.host.E}
    (hm : ι x + a • z ∈ glueLat Y X ι z u L₀ x₀) :
    ∃ x₁ ∈ hat L₀, ∃ b ∈ OA D, vA X x = x₁ + b • vA X x₀ ∧ inc D a = b * inc D (Tu D u)⁻¹ := by
  have hv := vA_mem_hat Y hm
  rw [vA_flat, mem_hat_glueLat] at hv
  obtain ⟨x₁, hx₁, b, hb, e⟩ := hv
  obtain ⟨e1, e2⟩ := flat_inj h e
  exact ⟨x₁, hx₁, b, hb, e1, e2⟩

theorem mem_flatSp (x : X.V) (a : D.host.E) : ι x + a • z ∈ flatSp Y X ι z := Submodule.add_mem_sup (LinearMap.mem_range_self ι x)
    (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self z))

set_option maxHeartbeats 1600000 in

theorem isGlueVec_of_isSDIn : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  obtain ⟨-, -, hsd⟩ := hSD

  have key : ∀ (p : X.V) (α : D.host.E) (q : X.V) (β : D.host.E),
      ι p + α • z ∈ glueLat Y X ι z u L₀ x₀ → ι q + β • z ∈ glueLat Y X ι z u L₀ x₀ →
      hA X (vA X p) (vA X q) - inc D α * cjA D (inc D β) * inc D (Tu D u) ∈ OA D := by
    intro p α q β hp hq
    rw [← inc_hD_flat h, inc_mem_iff]
    exact (hsd _ (mem_flatSp (ι := ι) (z := z) q β)).1 hq _ hp

  have hX : ∀ p : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → ι p + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    intro p hp
    rw [mem_glueLat_iff]
    exact ⟨p, hp, 0, by simp⟩
  have hg : ι x₀ + (Tu D u)⁻¹ • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [mem_glueLat_iff]
    exact ⟨0, by simp, 1, by simp⟩
  have hv : ∀ y : Fin X.rank → D.host.E,
      (fun i => inc D (y i)) = vA X ((Formalism.L2.Herm.crd X).symm y) := by
    intro y
    funext i
    simp [vA]
  have hrat : ∀ p q : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → Formalism.L2.Herm.crd X q ∈ L₀ →
      hA X (vA X p) (vA X q) ∈ OA D := by
    intro p q hp hq
    simpa using key p 0 q 0 (hX p hp) (hX q hq)

  have hright : ∀ f, (∀ y ∈ L₀, hA X f (fun i => inc D (y i)) ∈ OA D) →
      ∀ y ∈ hat L₀, hA X f y ∈ OA D := by
    intro f hf y hy
    refine hat_induction (p := fun y => hA X f y ∈ OA D) hf ?_ ?_ ?_ hy
    · show hA X f 0 ∈ OA D
      rw [hA_zero_right]
      exact zero_mem _
    · intro a b ha hb
      show hA X f (a + b) ∈ OA D
      rw [hA_add_right]
      exact add_mem ha hb
    · intro a ha b hb
      show hA X f (a • b) ∈ OA D
      rw [hA_smul_right]
      exact mul_mem (cjA_mem ha) hb
  have hint : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D := by
    intro x hx
    refine hright x fun y hy => hA_mem_of_forall (fun x' hx' => ?_) x hx
    rw [hv x', hv y]
    exact hrat _ _ (by simpa using hx') (by simpa using hy)

  have hz : ι 0 + (1 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [map_zero, zero_add]
    exact (hP 1).2 (one_mem _)
  obtain ⟨x₁, hx₁, b, -, e1, e2⟩ := coords_of_mem h hz
  have hb : b = inc D (Tu D u) := by
    rw [map_one] at e2
    calc b = b * (inc D (Tu D u)⁻¹ * inc D (Tu D u)) := by rw [inc_inv_mul, mul_one]
      _ = inc D (Tu D u) := by rw [← mul_assoc, ← e2, one_mul]
  have h0 : vA X (0 : X.V) = 0 := by simpa using vA_add X (0 : X.V) 0
  refine ⟨?_, hint, ?_, ?_, ?_⟩
  · rw [h0] at e1
    rw [← hb, eq_sub_of_add_eq' e1.symm]
    exact sub_mem_hat zero_mem_hat hx₁
  · refine hright (vA X x₀) fun y hy => ?_
    rw [hv y]
    simpa using key x₀ (Tu D u)⁻¹ _ 0 hg (hX _ (by simpa using hy))
  · have := key x₀ (Tu D u)⁻¹ x₀ (Tu D u)⁻¹ hg hg
    rwa [cjA_inc_inv, mul_assoc, inc_inv_mul, mul_one] at this
  ·

    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_sub_inc_mem_hat hlat.span_eq_top y
    obtain ⟨q, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y₀
    change y - vA X q ∈ hat L₀ at hy₀
    have hq : ι q + X.hD q x₀ • z ∈ glueLat Y X ι z u L₀ x₀ := by
      refine (hsd _ (mem_flatSp (ι := ι) (z := z) q (X.hD q x₀))).2 fun v hv' => ?_
      obtain ⟨p, hp, a, rfl⟩ := (mem_glueLat_iff v).1 hv'
      have hp' : vA X p ∈ hat L₀ := inc_mem_hat hp
      have h1 : hA X (vA X p) (vA X q) ∈ OA D := by
        rw [show vA X q = y - (y - vA X q) from (sub_sub_cancel y (vA X q)).symm, hA_sub_right]
        exact sub_mem (hy _ hp') (hint _ hp' _ hy₀)
      rw [← inc_mem_iff, inc_hD_flat h, ← hA_vA X q x₀, cjA_hA, vA_add, vA_smul, hA_add_left,
        hA_smul_left, map_mul (inc D)]
      convert h1 using 1
      linear_combination (-(inc D (a : D.host.E) * hA X (vA X x₀) (vA X q))) * inc_inv_mul u
    obtain ⟨x₂, hx₂, c, hc, e3, -⟩ := coords_of_mem h hq
    refine ⟨c, hc, ?_⟩
    have e4 : y - c • vA X x₀ = (y - vA X q) + x₂ := by
      rw [e3]
      abel
    rw [e4]
    exact add_mem_hat hy₀ hx₂

end GlobalTheory.AdIsom.SelfDualGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMovesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_congruent_of_two_lattice_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_two_moves | exact GlobalTheory.Ker.LevMove.levK_of_two_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_two_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateAdd
section
open GlobalTheory.FunObj

namespace GlobalTheory

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ A) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    show Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne (by omega : n ≠ j₀), chainTo_update_of_le k j₀ A n (by omega)]

theorem chainTo_update_succ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    chainTo (Function.update k j₀ A) (j₀ + 1) = A ∘ₗ chainTo k j₀ := by
  show Function.update k j₀ A j₀ ∘ₗ chainTo (Function.update k j₀ A) j₀ = _
  rw [Function.update_self, chainTo_update_of_le k j₀ A j₀ le_rfl]

theorem chainTo_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  intro V _ _ k j₀ A B n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [chainTo_update_succ, chainTo_update_succ, chainTo_update_succ, LinearMap.add_comp]
  | succ n hn ih =>
    show Function.update k j₀ (A + B) n ∘ₗ chainTo (Function.update k j₀ (A + B)) n =
      Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n + Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n
    have hne : n ≠ j₀ := by omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne, ih, LinearMap.comp_add]

example : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n :=
  chainTo_update_add

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmul
section
open GlobalTheory.FunObj

namespace GlobalTheory.ChainSmul

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (B : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ B) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    have hne : n ≠ j₀ := by omega
    show Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne hne, chainTo_update_of_le k j₀ B n (by omega)]

theorem chainTo_update_smul {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, j₀ < n → chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show Function.update k j₀ (c • A) n ∘ₗ chainTo (Function.update k j₀ (c • A)) n =
      c • (Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hne : n ≠ j₀ := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne, chainTo_update_smul k j₀ c A n h',
        LinearMap.comp_smul]
    · rw [Function.update_self, Function.update_self, chainTo_update_of_le k j₀ _ j₀ le_rfl,
        chainTo_update_of_le k j₀ _ j₀ le_rfl, LinearMap.smul_comp]

end GlobalTheory.ChainSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOverStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_eq_iff_idempotent_components_over : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  first | exact @GlobalTheory.LocHat.locL_eq_iff_idem | exact GlobalTheory.LocHat.locL_eq_iff_idem | (intros; apply GlobalTheory.LocHat.locL_eq_iff_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanAddSmulLatticeOfFrameCoeffsZmod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory

open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in
theorem mo_of_coef_mod : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ v ∈ I.Lf, ∀ (Se : Set (Fin r)) (Sb : Set (Fin k)), (∀ a, a ∉ Se → ZMod' I g (hA I (f0 a) v)) → (∀ a, ZMod' I g (hA I (e0 a) v)) → ZMod' I g (hA I z0 v) → (∀ i, i ∉ Sb → ZMod' I g (hA I (bwd i) v)) → (∀ i, ZMod' I g (hA I (bw i) v)) → v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (e0 '' Se ∪ bw '' Sb) := by
  intro I g r k e0 f0 z0 bw bwd ew h v hv Se Sb hf he hz hbd hb
  have hm := h.mem
  refine mem_Mo_of (exp h v hv) ?_
  classical
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : a ∈ Se
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.1 a).2 hv) (Or.inl ⟨a, ha, rfl⟩))
    · exact mL_Mo I (Zv I g (hf a ha) (hm.1 a).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun a _ => he a) (fun a _ => (hm.1 a).2))
  · exact mL_Mo I (Zv I g hz hm.2.1)
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ Sb
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.2.2 i).2 hv) (Or.inr ⟨i, hi, rfl⟩))
    · exact mL_Mo I (Zv I g (hbd i hi) (hm.2.2 i).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun i _ => hb i) (fun i _ => (hm.2.2 i).2))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  first | exact @GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | exact GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | (intros; apply GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinatePoincareSumHalfWittEqBump
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSum

variable {D : D7}

theorem finite_rat_mem {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := lattice_Mx D m n
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem mixS_poinX : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ x, d.mixS T ψ v.μ v.𝓕 (poinX ψ d T β) x 0 = β x := by
  intro D ψ hψ S S₀ T ρ d v β hβ x
  have h := v.covol
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ i1
  have hone : v.μ.real v.𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]

  have hfin : {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E | β (x + rat ξ) ≠ 0}.Finite := by
    refine (finite_rat_mem _ (hβ.supp.isCompact.image (continuous_sub_right x))).subset fun ξ hξ => ?_
    exact ⟨x + rat ξ, subset_tsupport β hξ, add_sub_cancel_left x (rat ξ)⟩

  have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) (poinX ψ d T β))) 0 =
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) := by
    intro a
    rw [d.integrandS_eq, poinX_coords, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplOH_Y_X, ← d.symplOH_extX_extY T x a,
      ← d.symplOH_extX_extY T (x + 2 • rat ξ) a, map_add (d.extX T), two_nsmul, map_add (d.extX T), GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, neg_add_cancel_left]
  have hF := hasSum_integral_of_summable_integral_norm (μ := v.μ.restrict v.𝓕)
    (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
      ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ)) (fun ξ => ?_) ?_
  · rw [HypDec.mixS]
    simp only [key]
    refine hF.unique ?_
    have h0 : ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * β (x + rat 0) ∂v.μ = β x := by
      simp only [rat_zero, map_zero, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, symplOH_zero_left, add_zero,
        AddChar.map_zero_eq_one, one_mul, setIntegral_const, hone, one_smul]
    rw [← h0]
    refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
      ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) ∂v.μ) 0 fun ξ hξ => ?_
    rw [integral_mul_const, GlobalTheory.Core.Rk.ThetaOf.integral_pair hψ d T h hξ, zero_mul]
  · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
    exact (hψc.comp (GlobalTheory.Core.Rk.ThetaOf.continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
  · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
    refine summable_of_finite_support (hfin.subset fun ξ hξ => ?_)
    exact fun h0 => (Function.mem_support.1 hξ) (by simp only [h0, norm_zero])

end GlobalTheory.BumpMixSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersectionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  first | exact @GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue | exact GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue | (intros; apply GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue <;> assumption)
end

