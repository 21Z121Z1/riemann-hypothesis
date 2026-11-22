import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.FrameTransport.Cong

variable {D : D7}

theorem adSwap_mem_intAf (x : StandardLatticesGL3.AE D) (hx : x ∈ StandardLatticesGL3.OhE D) :
    adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE x hx

theorem adSwap_inc (e : D.host.E) : adSwap D (StandardLatticesGL3.inc D e) = inclEAf D e := by
  have h1 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ e) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  have h2 : GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e := by
    show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e)) = _
    rw [h1, RingEquiv.symm_apply_eq]
    show _ = GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e)
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e)) = _
  rw [h2]
  rfl

theorem intG_entries {n : ℕ} (k : StandardLatticesGL3.GA D n) (hk : k ∈ GlobalTheory.NormSum.intG D n) : StandardLatticesGL3.IntG D k.1 := by
  have hmul : ∀ a b : GL (Fin n) (StandardLatticesGL3.AE D), (∀ i j, a.val i j ∈ StandardLatticesGL3.OhE D) → (∀ i j, b.val i j ∈ StandardLatticesGL3.OhE D) →
      ∀ i j, (a * b).val i j ∈ StandardLatticesGL3.OhE D := fun a b ha hb i j => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hb l j)
  let H : Subgroup (StandardLatticesGL3.GA D n) :=
    { carrier := {k | StandardLatticesGL3.IntG D k.1}
      mul_mem' := fun {a b} ha hb i j => by
        refine ⟨hmul a.1 b.1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j, ?_⟩
        have e : ((a * b : StandardLatticesGL3.GA D n) : GL (Fin n) (StandardLatticesGL3.AE D))⁻¹ = b.1⁻¹ * a.1⁻¹ := by
          rw [Subgroup.coe_mul, _root_.mul_inv_rev]
        rw [e]
        exact hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
      one_mem' := fun i j => by
        have h1 : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) i j ∈ StandardLatticesGL3.OhE D := fun i j => by
          rw [Matrix.one_apply]
          split_ifs
          exacts [Subring.one_mem _, Subring.zero_mem _]
        exact ⟨h1 i j, by rw [Subgroup.coe_one, inv_one]; exact h1 i j⟩
      inv_mem' := fun {a} ha i j => by
        refine ⟨(ha i j).2, ?_⟩
        rw [Subgroup.coe_inv, inv_inv]
        exact (ha i j).1 }
  exact (Subgroup.closure_le H).2 (fun k hk => hk) hk

theorem hatL_colLat_int {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (i : Fin n) :
    ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.completedColumnLattice_integral_frameCoords fr y hy i

theorem col_mem_hatL {n : ℕ} (fr : GL (Fin n) D.host.E) (j : Fin n) :
    (fun i => inclEAf D (fr.val i j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) :=
  Submodule.subset_span ⟨fun a => fr.val a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem eaf_mul_comm (a b : Lev.EAf D) : a * b = b * a := mul_comm a b

set_option maxHeartbeats 1000000 in
theorem hatL_colLat_of_int {n : ℕ} (fr : GL (Fin n) D.host.E) (z : Fin n → Lev.EAf D)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  have e : (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z =
      ∑ j, (⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j)) := by
    funext i
    rw [Finset.sum_apply]
    show ∑ j, (Formalism.UG.bc (inclEAf D) fr).val i j * z j =
      ∑ j, ((⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j))) i
    exact Finset.sum_congr rfl fun j _ => eaf_mul_comm _ _
  exact (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) e).mpr
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (col_mem_hatL fr j))

theorem mul_mem_spanIncl (𝔪 : Ideal (𝓞 D.host.E)) (a z : Lev.EAf D)
    (ha : a ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))))
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    a * z ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have h3 := Submodule.smul_mem _ (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha
  have e : (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • a = a * z := mul_comm z a
  exact e ▸ h3

theorem adSwap_hatId (𝔪 : Ideal (𝓞 D.host.E)) (c : StandardLatticesGL3.AE D) (hc : c ∈ SqNum.hatId D 𝔪) :
    adSwap D c ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have hle : SqNum.hatId D 𝔪 ≤ (Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))).toAddSubgroup.comap
        (adSwap D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have e : adSwap D (StandardLatticesGL3.inc D (b : D.host.E) * s) = inclEAf D (b : D.host.E) * adSwap D s :=
      (map_mul (adSwap D) _ _).trans (congrArg (· * adSwap D s) (adSwap_inc _))
    exact (congrArg (fun v => v ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) e).mpr
      (mul_mem_spanIncl 𝔪 _ _ (Submodule.subset_span ⟨b, hb, rfl⟩) (adSwap_mem_intAf s hs))
  exact hle hc

theorem hatL_smul_colLat {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D)
    (hw : ∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) :=
  GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice fr 𝔪 w hw

theorem hatL_transport {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D) (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L)) :
    uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  GlobalTheory.T.completedLatticeMap_idealMul_transport uf L Λ h 𝔪 y hy

theorem frConj_val {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ ((Formalism.UG.bc (adSwap D) k).val *ᵥ
      ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [frConj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem bc_adSwap_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    (Formalism.UG.bc (adSwap D) k).val i j = adSwap D (k.val i j) := rfl

theorem GL_mulVec_inv {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P.val *ᵥ (P⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem GL_inv_mulVec {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P⁻¹.val *ᵥ (P.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem frConj_sub {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y - y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ
      (((Formalism.UG.bc (adSwap D) k).val - 1) *ᵥ ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, GL_mulVec_inv (Formalism.UG.bc (inclEAf D) fr) y,
    frConj_val fr k y]

theorem bc_adSwap_sub_one_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    ((Formalism.UG.bc (adSwap D) k).val - 1) i j = adSwap D ((k.val - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [(map_one (adSwap D)).symm, (map_zero (adSwap D)).symm]

theorem frConj_stab {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, k.val i j ∈ StandardLatticesGL3.OhE D) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  rw [frConj_val]
  refine hatL_colLat_of_int fr _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (by rw [bc_adSwap_apply]; exact adSwap_mem_intAf _ (hk i j))
    (hatL_colLat_int fr y hy j)

theorem frConj_stab_iff {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : StandardLatticesGL3.IntG D k) (y : Fin n → Lev.EAf D) :
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  refine ⟨frConj_stab fr k (fun i j => (hk i j).1) y, fun h => ?_⟩
  have h2 := frConj_stab fr k⁻¹ (fun i j => (hk i j).2) _ h
  have e : (frConj fr k⁻¹).val *ᵥ ((frConj fr k).val *ᵥ y) = y := by
    rw [map_inv]; exact GL_inv_mulVec _ y
  exact e ▸ h2

theorem frConj_cong {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, (k.val - 1) i j ∈ SqNum.hatId D 𝔪) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  rw [frConj_sub fr k y]
  refine hatL_smul_colLat fr 𝔪 _ fun i => ?_
  show (∑ j, ((Formalism.UG.bc (adSwap D) k).val - 1) i j * ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) j) ∈ _
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 := mul_mem_spanIncl 𝔪 _ _ (adSwap_hatId 𝔪 _ (hk i j)) (hatL_colLat_int fr y hy j)
  rw [bc_adSwap_sub_one_apply k i j]
  exact h4

set_option maxHeartbeats 1000000 in

theorem conj_mem_congLev : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V fr uf Λ hL 𝔪 k hk hc hU
  have hM : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      uf⁻¹.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := fun x =>
    ((hL (uf⁻¹.val *ᵥ x)).trans (by rw [GL_mulVec_inv uf x])).symm
  have hg : ∀ x, (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x = uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg' : ∀ x, uf⁻¹.val *ᵥ ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x) = (frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) := by
    intro x
    rw [hg x, GL_inv_mulVec]
  refine ⟨hU, fun x => ?_, fun x hx => ?_⟩
  · refine (hM x).trans ((frConj_stab_iff fr k.1 (intG_entries k hk) _).trans ?_)
    exact ((hM ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x)).trans
      (Iff.of_eq (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (hg' x)))).symm
  · have hy := (hM x).1 hx
    have h5 := hatL_transport uf (colLat fr) Λ (fun v hv => (hL v).1 hv) 𝔪 _ (frConj_cong fr 𝔪 k.1 hc _ hy)
    have e : uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) - uf⁻¹.val *ᵥ x) =
        (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x - x := by
      exact (Matrix.mulVec_sub uf.val _ _).trans (congrArg₂ HSub.hSub (hg x).symm (GL_mulVec_inv uf x))
    exact Eq.mp (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) e) h5

end GlobalTheory.FrameTransport.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPathStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  first | exact @GlobalTheory.Nef.genPath_scaling | exact GlobalTheory.Nef.genPath_scaling | (intros; apply GlobalTheory.Nef.genPath_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSmallDict

def IsRootOne (ζ : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def IsAlgUnit (ζ : ℂ) : Prop :=
  ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1

variable {D : D7}

def IsStdLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i

def unitPt (S T : HSp D) (a : Formalism.L2.Theta.AE D) (o : ℕ) : WO S T := fun i j => if i.1 = o + j.1 then a else 0

def cosetFn {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T) : WO S T → ℂ := fun y =>
  if IsHalf a y ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - x i j)) then 1 else 0

def modul (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : Ideal (𝓞 D.host.E) :=
  ∏ w ∈ P, w.asIdeal ^ c w

def GoodIdem (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  IsIdemSum e P ∧ ∀ w ∈ P, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

theorem IsRootOne.one : IsRootOne 1 := ⟨1, one_pos, one_pow 1⟩

theorem IsRootOne.mul {a b : ℂ} (ha : IsRootOne a) (hb : IsRootOne b) : IsRootOne (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨n, hn, h'⟩ := hb
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, pow_mul, h, mul_comm m n, pow_mul, h', one_pow, one_pow, one_mul]⟩

theorem IsRootOne.ne_zero {a : ℂ} (ha : IsRootOne a) : a ≠ 0 := by
  obtain ⟨m, hm, h⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem IsRootOne.inv {a : ℂ} (ha : IsRootOne a) : IsRootOne a⁻¹ := by
  obtain ⟨m, hm, h⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩

theorem IsRootOne.isAlgUnit {a : ℂ} (ha : IsRootOne a) : IsAlgUnit a := by
  have h0 := ha.ne_zero
  obtain ⟨m, hm, h⟩ := ha
  have hq : a ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hm (by rw [h]; exact isAlgebraic_one))
  refine ⟨h0, hq, fun p _ lam => ?_⟩
  have h1 : (⟨a, hq⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have h2 : ‖lam ⟨a, hq⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  unfold lamC
  rw [dif_pos hq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2

theorem IsAlgUnit.mul {a b : ℂ} (ha : IsAlgUnit a) (hb : IsAlgUnit b) : IsAlgUnit (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, Qbar.mul_mem ha.2.1 hb.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam ha.2.1 hb.2.1, norm_mul, ha.2.2 p lam, hb.2.2 p lam, one_mul]⟩

end GlobalTheory.BotSmallDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtNegOfGramOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomPairData
variable {D : D7}

theorem sig_of_gram_one {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 ∧ (V.sig τ).1 = V.rank := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  have hq : (V.sig τ).2 = 0 := by
    by_contra hq
    let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
    have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
      Complex.one_re] at hk
    have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
      rw [Matrix.mul_apply, Complex.re_sum]
      exact Finset.sum_nonneg fun l _ => by
        rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
    linarith
  refine ⟨hq, ?_⟩
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum, hq] at this
  omega

open GlobalTheory.Grid (neg neg_gram) in

def negFrame (A : HSp D) : CptF (neg A) := fun τ r c =>
  Sum.elim (fun _ => (0 : ℂ)) (fun k => if (k : ℕ) = (c : ℕ) then 1 else 0) r

open GlobalTheory.Grid (neg) in
theorem negFrame_inl (A : HSp D) (τ : D.what₂.Tau) (a : Fin ((neg A).sig (tauE D τ)).1) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inl a) c = 0 := rfl

open GlobalTheory.Grid (neg) in
theorem negFrame_inr (A : HSp D) (τ : D.what₂.Tau) (k : Fin ((neg A).sig (tauE D τ)).2) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inr k) c = if (k : ℕ) = (c : ℕ) then 1 else 0 := rfl

open GlobalTheory.Grid (neg neg_gram) in
theorem jpq_mul_negFrame (A : HSp D) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq ((neg A).sig (tauE D τ)).1 ((neg A).sig (tauE D τ)).2 * negFrame A τ = -negFrame A τ := by
  ext r c
  rcases r with a | b
  · rw [Matrix.neg_apply, show negFrame A τ (Sum.inl a) c = 0 from rfl, neg_zero, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun x _ => by
      rcases x with x | x
      · rw [show negFrame A τ (Sum.inl x) c = 0 from rfl, mul_zero]
      · simp [Formalism.UG.Jpq]
  · simp only [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      negFrame_inl, negFrame_inr, mul_zero, Finset.sum_const_zero, Matrix.neg_apply, Matrix.zero_apply, zero_mul, zero_add,
      Matrix.one_apply, neg_mul, ite_mul, one_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

open GlobalTheory.Grid (neg neg_gram) in
theorem negFrame_conj_mul (A : HSp D) (hg : A.gram = 1) (hA : A.SigOK) (τ : D.what₂.Tau) :
    (negFrame A τ)ᴴ * negFrame A τ = 1 := by
  obtain ⟨hq, hp⟩ := sig_of_gram_one hg hA (tauE D τ)
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  have e1 : ∀ x, star (negFrame A τ (Sum.inl x) a) * negFrame A τ (Sum.inl x) b = 0 := fun x => by
    rw [show negFrame A τ (Sum.inl x) a = 0 from rfl, star_zero, zero_mul]
  have e2 : ∀ x : Fin ((neg A).sig (tauE D τ)).2, star (negFrame A τ (Sum.inr x) a) * negFrame A τ (Sum.inr x) b =
      if (x : ℕ) = a ∧ (x : ℕ) = b then 1 else 0 := fun x => by
    rw [negFrame_inr, negFrame_inr]
    by_cases h1 : (x : ℕ) = a <;> by_cases h2 : (x : ℕ) = b <;> simp [h1, h2]
  rw [Finset.sum_eq_zero fun x _ => e1 x, zero_add, Finset.sum_congr rfl fun x _ => e2 x]
  have hk : (a : ℕ) < ((neg A).sig (tauE D τ)).2 := by
    show (a : ℕ) < (A.sig (tauE D τ)).1
    rw [hp]; exact a.2
  rw [Finset.sum_eq_single ⟨a, hk⟩]
  · by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg]; rintro ⟨-, h2⟩; exact h (Fin.ext h2)
  · intro x _ hx; rw [if_neg]; rintro ⟨h1, -⟩; exact hx (Fin.ext h1)
  · simp

open GlobalTheory.Grid (neg neg_gram) in
theorem gramAt_neg_of_gram_one {A : HSp D} (hg : A.gram = 1) (τ : D.what₂.Tau) : gramAt D (neg A) τ = -1 := by
  ext a b
  simp only [gramAt, neg_gram, hg, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn) in

theorem exists_pair {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S}
    (h : X.Is ψ θ α β νH S) (hstd : X.rA.IsStd) (hA : A.SigOK) (h1 : 1 ≤ A.rank) (h1' : 1 ≤ A'.rank) (t : T) :
    ∃ (cA : CptF (neg A)) (a : GL (Fin (neg A).rank) (AE D)) (ν : Measure (WO (neg A) WW)) (𝓕 : Set (WO (neg A) WW)),
      Pair ψ θ (neg A) WW (β t) (β t / α t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) ν 𝓕 := by
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (neg A) WW
  have hg := hstd.1
  have hgn : ∀ τ, gramAt D (neg A) τ = -1 := gramAt_neg_of_gram_one hg
  have hs : ∀ τ, X.rA.s τ = 1 := fun τ => (hstd.2.2 τ).1
  refine ⟨negFrame A, 1, ν, 𝓕, ⟨⟨h1, h1', ?_, h.isVac.2.inf, sigOK_sgn true hA, fun τ => ?_,
    fun τ => isCartanInv_sgn true _ τ (h.rigA.2.2 τ).1, fun τ => (h.rigW.2.2 τ).1, fun τ => ?_⟩, ?_, fun τ => ?_, h.weil t, hν⟩⟩
  · exact h.rank.symm
  · rw [Matrix.mul_assoc, jpq_mul_negFrame, Matrix.mul_neg, negFrame_conj_mul A hg hA, hgn]
  · show negFrame A τ * -X.rA.s τ = _
    rw [hs, jpq_mul_negFrame, Matrix.mul_neg, Matrix.mul_one]
  · intro w
    refine ⟨fun _ => false, ?_⟩
    simp only [JR, neg_gram, hg]
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rw [hgn, hs]
    simp [compAt]

open GlobalTheory.Grid (neg) in

theorem one_le_bot (i j : Fin D.R.m) : 1 ≤ botBig D i j ∧ 1 ≤ botSmall D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  have h2 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr : Odd D.R.r := by
    have := GlobalTheory.ChiGrid.odd_sLen D
    simp only [GlobalTheory.ChiGrid.sLen] at this
    exact (Nat.odd_add.1 this).2 (by decide)
  obtain ⟨w, hw⟩ := hr
  have hi := i.2
  have hj := j.2
  simp only [botBig, botSmall, rankV, GlobalTheory.ChiGrid.sLen]
  constructor <;> omega

end GlobalTheory.BottomPairData

open GlobalTheory.BottomPairData in

theorem GlobalTheory.BottomPairData.pair_data : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T, ∃ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)), Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX hA t
  have hb := one_le_bot (D := D) i j
  exact exists_pair X (GlobalTheory.BottomIPData.isBottomTri_is hX) hX.std hA (hX.rank ▸ hb.1) (hX.rank' ▸ hb.2) t

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_eq : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
  ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.FinIdlRead.chr_finIdl | exact GlobalTheory.FinIdlRead.chr_finIdl | (intros; apply GlobalTheory.FinIdlRead.chr_finIdl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAtStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertDual.latAtV_selfDual | exact GlobalTheory.InertDual.latAtV_selfDual | (intros; apply GlobalTheory.InertDual.latAtV_selfDual <;> assumption)
end

