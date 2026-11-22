import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeet
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueVecLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem mem_of_coords {L₀ : Lat X} {x₀ x : X.V} {t : D.host.E}
    (h1 : t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (h2 : Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ := by
  obtain ⟨a, ha⟩ := h1
  refine (mem_glueLat _).2 ⟨_, h2, a, ?_⟩
  change _ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _
  rw [ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]
  abel

theorem coords_of_mem_hat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ x : X.V}
    {t : D.host.E} (hy : vA Y (ι x + t • z) ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀))) :
    t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
      Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ := by
  obtain ⟨x₁, hx₁, a, ha, e⟩ := (mem_hat_glueLat _).1 hy
  rw [vA_flat] at e
  obtain ⟨e1, e2⟩ := flat_inj h e
  have e3 : a = inc D (t * Tu D u) := by
    rw [RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]
  refine ⟨(inc_mem_iff _).1 (e3 ▸ ha), (inc_mem_hat_iff hL _).1 ?_⟩
  change vA X (x - (t * Tu D u) • x₀) ∈ _
  have e4 : vA X (x - (t * Tu D u) • x₀) = x₁ := by
    rw [sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]
  rwa [e4]

theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

theorem mem_flatSp (y : Y.V) : y ∈ flatSp Y X ι z ↔ ∃ (x : X.V) (t : D.host.E), y = ι x + t • z := by
  rw [flatSp, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩

theorem glueLat_fg {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) : (glueLat Y X ι z u L₀ x₀).FG := by
  refine Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)
  have e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
      L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀
      rwa [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hL.fg.map _

theorem span_glueLat {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) = flatSp Y X ι z := by
  have h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) := by
    intro x
    obtain ⟨y, rfl⟩ := (Formalism.L2.Herm.crd X).symm.surjective x
    have hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E)) := hL.span_eq_top ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, -, a, rfl⟩ := (mem_glueLat y).1 hy
    refine (mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩
    rw [map_add, map_smul, smul_add, smul_smul]
    abel
  · obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
    refine add_mem (h1 x) (Submodule.smul_mem _ t ?_)
    have h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) :=
      Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)
    have h3 := Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))
    rwa [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul] at h3

theorem isSDIn_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) := by
  refine ⟨glueLat_fg hL x₀, span_glueLat hL x₀, fun y hy => ?_⟩
  obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
  have key := mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)
  rw [← vA_flat] at key
  constructor
  · intro hm x' hx'
    rw [← inc_mem_iff, ← hA_vA]
    exact key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')
  · intro H
    have h1 := coords_of_mem_hat h hL (key.2 (hA_mem_of_forall ?_))
    · exact mem_of_coords h1.1 h1.2
    · rintro _ ⟨x', hx', rfl⟩
      change hA Y (vA Y x') _ ∈ _
      rw [hA_vA, inc_mem_iff]
      exact H x' hx'

theorem capX_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
      rw [zero_smul, add_zero]; exact hx
    have h2 := ((mem_iff_coords h hL x 0).1 h1).2
    rwa [zero_mul, zero_smul, sub_zero] at h2
  · intro hy
    obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y
    exact ⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩

theorem isPrim_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsPrim Y z (glueLat Y X ι z u L₀ x₀) := by
  intro a
  have e : a • z = ι 0 + a • z := by rw [map_zero, zero_add]
  rw [e, mem_iff_coords h hL, ← inc_mem_hat_iff hL, ← inc_mem_iff, ← inc_mem_iff]
  change _ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _
  rw [zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]
  generalize inc D a = b
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := hg.pair _ h2
    rw [hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu] at h3
    have h4 := mul_mem (cjA_mem h1) hg.norm
    rw [RingHom.map_mul, cjA_inc_Tu] at h4
    rw [← cjA_mem_iff]
    convert neg_mem (add_mem h3 h4) using 1
    linear_combination (-(cjA D b)) * inc_inv_mul u
  · intro hb
    refine ⟨mul_mem hb (inc_Tu_mem u), ?_⟩
    rw [← neg_mul, ← smul_smul]
    exact smul_mem_hat (neg_mem hb) hg.mul_mem

theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL hg, capX_glueLat h hL x₀⟩

end GlobalTheory.GlueVecLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

variable {D : D7}

theorem eq_of_ev {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {a b : AE D}
    (hi : infPart D a = infPart D b) (hf : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  refine sub_eq_zero.1 (hΦ.ext (a - b) (by rw [RingHom.map_sub, hi, sub_self]) (FiniteAdeleRing.ext _ fun Q => ?_))
  rw [ev_sub, hf Q, sub_self]
  rfl

theorem eq_one_of_supp {w : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {χ : (AE D)ˣ →* Circle}
    (h : Formalism.IndefR.Mult.IsPrimeIdem w e f) (hu : GlobalTheory.LFun.UnrAt χ w) (x : (AE D)ˣ)
    (hx : e * ((x : AE D) - 1) = (x : AE D) - 1) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : χ x = 1 := by
  obtain ⟨y, hy, rfl⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart h)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem h) x hx
  have hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) =
      GlobalTheory.LFun.compAt D.host.F w (finPart D ((GlobalTheory.LFun.locIdele D.host.F w y)⁻¹ : (AE D)ˣ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy]; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h1 w
  have a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy']; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h2 w
  have hun : Formalism.L2.Host.IsUnitAt w y :=
    GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2
  have := hu y hun
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.UnramFromOnePrime

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

set_option maxHeartbeats 1000000 in

theorem unramAt_of_unrAt_one : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  classical
  intro D ν _ hR v ε hε w hw hu x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨hd, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have pc := place_comp hΦ hε
  have pc' := place_comp hΦ hε'
  have hfε : f = algebraMap (AF D.host.F) (AE D) ε := by
    rw [hf]
    refine eq_of_ev hΦ (by rw [pc.1, pc'.1]) fun Q => ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [pc.2.1 Q hQ, pc'.2.1 Q hQ]
    · rw [pc.2.2 Q hQ, pc'.2.2 Q hQ]
  have hev : ∀ Q, Φ e Q = if Q = w then 1 else 0 := fun Q => by
    split_ifs with hQ
    · rw [hQ]; exact hd.2.1
    · exact hd.2.2 Q hQ
  have hee : e * e = e := eq_of_ev hΦ (by rw [RingHom.map_mul, hd.1, zero_mul]) fun Q => by
    rw [ev_mul, hev Q]
    split_ifs <;> simp
  have key : (1 - e) * (1 - cA D e) * f = 0 := by
    rcases hp with ⟨-, hfe⟩ | ⟨hfe, -, -⟩
    · have hc2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
      rw [hfe]
      linear_combination (cA D e - 1) * hee + (e - 1) * hc2
    · rw [hfe]
      linear_combination (cA D e - 1) * hee
  have hfc : cA D f = f := by rw [hfε]; exact cA_algebraMap ε
  have hx' : f * ((x : AE D) - 1) = (x : AE D) - 1 := by rw [hfε]; exact hx
  have int1 : ∀ Q, Φ (x : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h1
  have int2 : ∀ Q, Φ ((x⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h2
  obtain ⟨y, hy, hys⟩ := GlobalTheory.UnrOffLevels.exists_glue hee x
  have hxx : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv x
  have hyi : ((y⁻¹ : (AE D)ˣ) : AE D) = e * ((x⁻¹ : (AE D)ˣ) : AE D) + (1 - e) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy]
    linear_combination (e * e) * hxx + (2 - (x : AE D) - ((x⁻¹ : (AE D)ˣ) : AE D)) * hee
  have cut_int : ∀ z : AE D, (∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E) →
      ∀ Q, Φ (e * z + (1 - e)) Q ∈ Q.adicCompletionIntegers D.host.E := fun z hz Q => by
    rw [ev_add, ev_mul, ev_sub, ev_one, hev Q]
    split_ifs
    · rw [one_mul, sub_self, add_zero]; exact hz Q
    · rw [zero_mul, sub_zero, zero_add]; exact one_mem _
  have iy1 : ∀ Q, Φ (y : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by rw [hy]; exact cut_int _ int1
  have iy2 : ∀ Q, Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by
    rw [hyi]; exact cut_int _ int2
  have hνy : ν y = 1 := eq_one_of_supp hp hu y hys ((hΦ.int _).2 iy1) ((hΦ.int _).2 iy2)
  obtain ⟨z, hzdef⟩ : ∃ z : (AE D)ˣ, z = x * y⁻¹ := ⟨_, rfl⟩
  have iz1 : finPart D (z : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    rw [hzdef, Units.val_mul, ev_mul]; exact mul_mem (int1 Q) (iy2 Q)
  have iz2 : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    have hzi : (z⁻¹ : (AE D)ˣ) = y * x⁻¹ := by rw [hzdef, _root_.mul_inv_rev, inv_inv y]
    rw [hzi, Units.val_mul, ev_mul]; exact mul_mem (iy1 Q) (int2 Q)
  have hz1 : (z : AE D) - 1 = (1 - e) * f * ((x : AE D) - 1) := by
    have hzv : (z : AE D) = (x : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) := by rw [hzdef, Units.val_mul]
    rw [hzv, hyi]
    linear_combination e * hxx - (1 - e) * hx'
  have hcz : cA D (z : AE D) - 1 = (1 - cA D e) * f * (cA D (x : AE D) - 1) := by
    have := congrArg (cA D) hz1
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, hfc] at this
    exact this
  have hconj : ν (Units.map (cA D : AE D →* AE D) z) = (ν z)⁻¹ := GlobalTheory.ConjAdjWeil.chi_conj hR z
  obtain ⟨cz, hczdef⟩ : ∃ cz : (AE D)ˣ, cz = Units.map (cA D : AE D →* AE D) z := ⟨_, rfl⟩
  rw [← hczdef] at hconj
  have hcv : (cz : AE D) = cA D (z : AE D) := by rw [hczdef]; rfl
  have hcvi : ((cz⁻¹ : (AE D)ˣ) : AE D) = cA D ((z⁻¹ : (AE D)ˣ) : AE D) := by rw [hczdef, ← map_inv]; rfl
  have hνcz : ν cz = 1 := by
    refine eq_one_of_supp hp hu cz ?_ ?_ ?_
    · rw [hcv, hcz]
      linear_combination (-(cA D (x : AE D) - 1)) * key
    · rw [hcv]; exact finPart_cA_mem iz1
    · rw [hcvi]; exact finPart_cA_mem iz2
  have hνz : ν z = 1 := inv_eq_one.1 (hconj.symm.trans hνcz)
  have hxyz : x = y * z := by rw [hzdef, mul_comm x, mul_inv_cancel_left]
  rw [hxyz, map_mul, hνy, hνz, one_mul]

end GlobalTheory.UnramFromOnePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

theorem smul_sum_sub_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (cf : Fin n → ℂ) (bv : Fin n → V)
    (s : ℂ) (i : Fin n) (h1 : cf i = 1) (h0 : ∀ j, i < j → cf j = 0) :
    s • ∑ j, cf j • bv j - s • bv i ∈ Submodule.span ℂ (bv '' {j | j < i}) := by
  classical
  have e1 : s • ∑ j, cf j • bv j - s • bv i = ∑ j, (s * (cf j - if j = i then 1 else 0)) • bv j := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp
  rw [e1]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases lt_trichotomy j i with hj | rfl | hj
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · simp [h1]
  · simp [h0 j hj, hj.ne']

theorem exists_lift_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {σ' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di i) ty P) (hP' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di j) ty P')
    {p : ℕ} (hp : p.Prime)
    {y y₁ y₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy₁ : y₁ = F.u j P') (hy₂ : y₂ = F.u j P')
    (C C' : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G))
    (ψ' : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₂)
    (ψp' : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₂ ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hC' : ∀ a ∈ C', a ^ p ^ 2 = 1)
    (hI : Formalism.L2.Pj.IsHkIsog p y y₁ C ψ ψp) (hI' : Formalism.L2.Pj.IsHkIsog p y y₂ C' ψ' ψp') :
    ∃ (gam gam' : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ a b, (F.Di j).EF (gam' a) (gam' b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam' a) = h' (P a)) ∧
      (∀ (w : Fin g → ℂ) (v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h' w) (v ≫ ψ' ≫ pullback.fst _ _)) ∧
      (h = h' → C = C') := by
  subst hy hy₁ hy₂
  obtain ⟨gam, h, h1, h2, -, h4⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam', h', h1', h2', -, h4'⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C' ψ' ψp' hP hP' hp hC' hI'
  refine ⟨gam, gam', h, h', h1, h2, h1', h2', fun w v hvs hd => ?_, fun hh => ?_⟩
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    refine ⟨?_, ?_⟩
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left :=
        fun z => by
          rw [← Category.assoc, hI.2.2.1, h4]
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ' ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ' ≫ pullback.fst _ _ = (F.ex j P' (h' z)).left :=
        fun z => by
          rw [← Category.assoc, hI'.2.2.1, h4']
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h'.toLinearMap w _).1 d1
  · rw [← hI.2.2.2.2.2.1, ← hI'.2.2.2.2.2.1]
    congr 1
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := F.ex_onto i P hP x
    rw [← h4, ← h4', hh]

end GlobalTheory.HeckeInj

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in

theorem eq_of_hkRelFr_frBor : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hU P p i hHP k x C C' z z' w t t' hz hz' ht ht' hB hB'
  obtain ⟨-, -, hall, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨Pm, -, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨k'', x'', t'', hB''⟩ := hall w
  obtain ⟨Pm'', -, per'', hPx'', hv'', -⟩ := hpt k'' x''
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hz
  obtain ⟨ψ', ψp', hI', hL', -⟩ := hz'
  have hpp : p.Prime := hHP.2.2.2.1
  have hwx : w.x = F.u (ik k'') Pm'' := hB''.1.trans hPx''
  obtain ⟨gam, gam', h, h', hiso, hh, hiso', hh', hder, hker⟩ :=
    exists_lift_pair F (ik k) (ik k'') Pm Pm'' per per'' hpp hPx (hB.1.trans hwx) (hB'.1.trans hwx) C.1 C'.1
      ψ ψp ψ' ψp' (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C.2 ha)
      (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C'.2 ha) hI hI'
  choose c'' hc''1 hc''2 hc''3 using hB''.2.1
  let bv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ) := fun τ j =>
    ∑ i, Formalism.L2.Pj.toC (c'' τ j i) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ)
  have hdw : ∀ τ j, IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (bv τ j) (w.u τ j) := fun τ j =>
    (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ ((U.un k'' x'').u τ) _ (hv'' τ) (c'' τ j)
      (w.u τ j)).1 (hPx'' ▸ hc''3 τ j)
  have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm'' per''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
    have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
      apply RingHom.ext
      intro a
      ext <;> simp [epsMul]
    rw [e0]
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  letI : Field (Formalism.L2.Pj.CAt σ) := inferInstanceAs (Field ℂ)
  have col : ∀ (zz : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ)) (tt : Formalism.L2.Pj.Ix Dw → (Formalism.L2.Pj.CAt σ)ˣ)
      (ψ0 : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom zz.x)
      (h0 : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ τ j, Formalism.L2.Pj.IsLieImageH p ψ0 ((U.un k x).u τ j) (zz.u τ j)) →
      (∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (U.un k x).x),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (h0 w) (v ≫ ψ0 ≫ pullback.fst _ _)) →
      (∀ j, j ≠ none → tt j = 1) → Formalism.L2.Pj.FrBor tt w zz →
      ∀ τ m, h0 (Pi.single (e.symm ⟨τ, m⟩) 1) - (p : ℂ) • bv τ m ∈
        Submodule.span ℂ (bv τ '' {j | j < m}) := by
    intro zz tt ψ0 h0 hL0 hder0 ht0 hB0 τ m
    choose cf hcf1 hcf2 hcf3 using hB0.2.1
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL0 τ m
    have d2 := hder0 (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ (w.u τ) _ (hdw τ) (cf τ m)
      (zz.u τ m)).1 (hwx ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ zz.u τ m = wv ≫ ψ0 ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3]
    refine smul_sum_sub_mem_span (fun j => Formalism.L2.Pj.toC (cf τ m j)) (bv τ) _ m ?_ fun j hj => ?_
    · show Formalism.L2.Pj.toC (cf τ m m) = 1
      rw [hcf1 τ m, ht0 _ (by simp)]
      rfl
    · show Formalism.L2.Pj.toC (cf τ m j) = 0
      rw [hcf2 τ m j hj]
      rfl
  obtain ⟨Hm, -, hpos, hHm⟩ := per''.2.2.2.2
  have hform : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm (h' x) (h' y) :=
    GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family Pm per.2.2.2.1 Hm h.toLinearMap h'.toLinearMap fun a b => by
      simp only [LinearEquiv.coe_coe]
      rw [← hh, ← hh, ← hh', ← hh', hHm, hHm, hiso, hiso']
  have hhh := GlobalTheory.T.eq_of_flag_of_hermForm_preserving e Hm hpos h h' hform bv (p : ℂ) hp0
    (col z t ψ h hL (fun w v a b => (hder w v a b).1) ht hB)
    (col z' t' ψ' h' hL' (fun w v a b => (hder w v a b).2) ht' hB')
  exact Subtype.ext (hker hhh)

end GlobalTheory.HeckeInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAction_fockOperators_scalars_trace : ∀ D : D7, GlobalTheory.ChainFr.LieFockAll D := by
  first | exact @GlobalTheory.LieScalar.lieFockAll | exact GlobalTheory.LieScalar.lieFockAll | (intros; apply GlobalTheory.LieScalar.lieFockAll <;> assumption)
end

