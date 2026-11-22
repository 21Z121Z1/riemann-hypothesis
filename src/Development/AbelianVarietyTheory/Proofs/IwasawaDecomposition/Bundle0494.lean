import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.GlobalTheory.GL4.PZBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
import Formalism.LocalToGlobal.Columns.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunction
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.IntSpanDelW

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality

variable {ι : Type} [Fintype ι] {n : ℕ}

def evM {p : ℕ} [Fact p.Prime] (P : MvPolynomial (ι × Fin n × Fin n) ℂ_[p]) :
    (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p] :=
  fun y => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem ten_int_map (R : Type) [CommRing R] (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom R) (f τ)) =
      MvPolynomial.map (Int.castRingHom R) (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.L2.Forms.ten Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

theorem prod_eval_eq_evM {p : ℕ} [Fact p.Prime] (f : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (y : ι → Matrix (Fin n) (Fin n) ℂ_[p]) :
    ∏ τ, MvPolynomial.eval (fun k : Fin n × Fin n => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)) =
      evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Formalism.MainNotions.flipTwoThree.ten f)) y := by
  unfold evM Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
  rfl

theorem mem_vlIntSpan_iff {K : Type} [Field K] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl)
    (lam : ι → DomWeight n) (Z : ZBasis lam) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    P ∈ vlIntSpan σ Pl w lam ↔ ∃ c : Z.J0 → K, (∀ i, c i ∈ intW Pl w) ∧
      P = ∑ i, σ (c i) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) := by
  constructor
  · intro hP
    induction hP using AddSubgroup.closure_induction with
    | mem P hP =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hP
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : K), fun i => mul_mem hr (intCast_mem _ _), ?_⟩
      rw [ten_int_map, ← hz, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      refine ⟨c + c', fun i => add_mem (hc i) (hc' i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨-c, fun i => neg_mem (hc i), ?_⟩
      simp [neg_smul, Finset.sum_neg_distrib]
  · rintro ⟨c, hc, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ r ∈ intW Pl w,
        σ r • MvPolynomial.map (Int.castRingHom ℂ) x ∈ vlIntSpan σ Pl w lam := by
      intro x hx r hr
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨r, f, hr, hf, ?_⟩
        rw [ten_int_map]
      | zero =>
        rw [map_zero, smul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add, smul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [map_zsmul, smul_comm]
        exact zsmul_mem hx a
    refine sum_mem fun i _ => key _ ?_ _ (hc i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem mem_delW_iff {p : ℕ} [Fact p.Prime] (lam : ι → DomWeight n) (Z : ZBasis lam)
    (F : (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p]) :
    F ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) ↔ ∃ d : Z.J0 → ℂ_[p], (∀ i, ‖d i‖ ≤ 1) ∧
      F = fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y := by
  constructor
  · intro hF
    induction hF using AddSubgroup.closure_induction with
    | mem F hF =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hF
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, fun τ => hf τ, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : ℂ_[p]), fun i => ?_, ?_⟩
      · rw [norm_mul]
        exact mul_le_one₀ hr (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [prod_eval_eq_evM, ← hz]
        simp only [evM, map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    | zero => exact ⟨0, fun _ => by simp, by funext y; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨d', hd', rfl⟩ := hy
      refine ⟨d + d', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd i) (hd' i)), ?_⟩
      funext v
      simp [add_mul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨-d, fun i => by rw [Pi.neg_apply, norm_neg]; exact hd i, ?_⟩
      funext v
      simp [neg_mul, Finset.sum_neg_distrib]
  · rintro ⟨d, hd, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ a : ℂ_[p], ‖a‖ ≤ 1 →
        (fun y => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) y) ∈
          WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) := by
      intro x hx a ha
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨a, f, ha, fun τ => hf τ, ?_⟩
        funext y
        rw [prod_eval_eq_evM]
      | zero =>
        have e : (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) 0) y) = 0 := by
          funext y
          simp [evM]
        rw [e]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (x + y)) v) =
            (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) +
              (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) y) v) := by
          funext v
          simp [evM, mul_add]
        rw [e]
        exact add_mem hx hy
      | smul z x _ hx =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (z • x)) v) =
            z • (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) := by
          funext v
          simp only [evM, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact zsmul_mem hx z
    have e : (fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) =
        ∑ i, (fun y => d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) := by
      funext y
      simp [Finset.sum_apply]
    rw [e]
    refine sum_mem fun i _ => key _ ?_ _ (hd i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem map_mem_vlIntSpan_iff_delW : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  classical
  intro K ι _ _ _ σ Pl w p _ φ hφ n lam G hG
  choose r e hr using fun τ => exists_weylBasis n (lam τ).natW (natW_anti (lam τ))
  set Z := zOf lam e with hZ
  have hG' : G ∈ Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (Z.bZ i)) := by
    rw [Z.span_F K]
    exact hG
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hG'
  have hmap : ∀ (L : Type) [Field L] (s : K →+* L), MvPolynomial.map s G =
      ∑ i, s (c i) • MvPolynomial.map (Int.castRingHom L) (Z.bZ i) := by
    intro L _ s
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, ← MvPolynomial.smul_eq_C_mul]
    have h : s.comp (Int.castRingHom K) = Int.castRingHom L := RingHom.ext_int _ _
    rw [h]
  show _ ↔ evM (MvPolynomial.map φ G) ∈ _
  rw [mem_vlIntSpan_iff σ Pl w lam Z, mem_delW_iff lam Z]
  constructor
  · rintro ⟨c', hc', he⟩
    have hcc : c = c' := by
      rw [hmap ℂ σ] at he
      have h0 : ∑ i, (σ (c i) - σ (c' i)) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self]
      funext i
      exact σ.injective (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ) _ h0 i))
    subst hcc
    refine ⟨fun i => φ (c i), fun i => (hφ _).1 (hc' i), ?_⟩
    funext y
    rw [hmap ℂ_[p] φ]
    simp [evM, MvPolynomial.smul_eval]
  · rintro ⟨d, hd, he⟩
    have hpoly : MvPolynomial.map φ G = ∑ i, d i • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) := by
      apply MvPolynomial.funext
      intro x
      have h1 := congrFun he (fun τ a b => x (τ, a, b))
      rw [map_sum]
      simp only [MvPolynomial.smul_eval]
      exact h1
    rw [hmap ℂ_[p] φ] at hpoly
    have hcd : ∀ i, φ (c i) = d i := by
      have h0 : ∑ i, (φ (c i) - d i) • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hpoly, sub_self]
      exact fun i => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ_[p]) _ h0 i)
    exact ⟨c, fun i => (hφ _).2 ((hcd i).symm ▸ hd i), hmap ℂ σ⟩

end GlobalTheory.Mem.IntSpanDelW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZeroContentPlacesIffOverOfNonvanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.WWUnique

theorem aeval_map_nablaX {Lt : Type} [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.aeval (R := ℂ_[l]) (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2)) :
          MvPolynomial (KM.XZ Lt N0 N1) ℂ_[l]))
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N1 nu I)) =
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.Gxz N0 N1 nu I) := by
  simp only [KM.nablaX, KM.Gxz, KM.minorXZ, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  simp [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul]

theorem ww_unique : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  intro D p _ N0 N1 hN nu hnu Th ph ph' κ Q hQ h I
  classical
  haveI : Finite (KM.ColChoice N1 nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N1 nu) := Fintype.ofFinite _
  let J : ((Bool × HH D) × Fin N0 × Fin N1 →₀ ℕ) → ℂ_[p] :=
    fun m => (m.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff m Th
  let σ : (Bool × HH D) × ℕ × Fin N1 → MvPolynomial (KM.XZ (Bool × HH D) N0 N1) ℂ_[p] :=
    fun v => ∑ a : Fin N0, MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2))
  let L : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) :=
    ph ∘ₗ GlobalTheory.KFormCore.jetL J ∘ₗ (MvPolynomial.aeval (R := ℂ_[p]) σ).toLinearMap
  have hL : ∀ J' : KM.ColChoice N1 nu, L (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu J')) =
      ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu J')) := by
    intro J'
    simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, σ]
    rw [aeval_map_nablaX, GlobalTheory.KFormCore.applyAt0_eq]
  have hLD : ∀ y, L (GL3Columns.DeX N1 nu y) = GL3Columns.applyQ p N0 N1 Th Q y := by
    intro y
    rw [GL3Columns.ww_holds D p N0 N1 nu Th ph Q hQ y, GL3Columns.wwCB_holds D ℂ_[p] N1 nu y, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hL, smul_eq_mul]
  let ψ : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) := ph' - κ • L
  have hψ : ∀ y, ψ (GL3Columns.DeX N1 nu y) = 0 := by
    intro y
    let e := Equiv.ofBijective (tauPl D) (tauPl_bij D)
    let y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p] := fun τ => Matrix.of fun a b => y (e.symm τ) a b
    have hy : GL3Columns.DeX N1 nu y = GL3Columns.DeX N1 nu (fun s => GL3Columns.colsOf (y' (tauPl D s))) := by
      unfold GL3Columns.DeX
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
      congr 1
      ext i j
      have hj : (j : ℕ) < N1 :=
        lt_of_lt_of_le j.2 ((YoungDiagram.colLen_anti _ 0 c (Nat.zero_le _)).trans ((hnu s).trans hN))
      have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
      simp [GL3Columns.colsOf, hj, y', hs]
    rw [hy]
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, h, hLD, smul_eq_mul, sub_self]
  have h4 := GL3Columns.wwInj_holds D p N1 nu ψ hψ I
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h4
  exact sub_eq_zero.mp h4

end GlobalTheory.KForm.WWUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliserStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openLevel_cutByCosetStabiliser : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q), ThetaOpen Θ → ∀ (C : ∀ P : Q, Set (Sp E n)), (∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) → ThetaOpen (GlobalTheory.Mem.Col2.ChEx.cutQ Θ C) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | exact GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | (intros; apply GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.aaUnit_sall | exact GlobalTheory.Mem.Col2.AdT.aaUnit_sall | (intros; apply GlobalTheory.Mem.Col2.AdT.aaUnit_sall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | exact GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | (intros; apply GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem mem_sgL_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (PP : Pl X.toD7.host.E) :
    PP ∈ sgL X I U t ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t := by
  rw [hL.Pg, hL.Q t, Col2.ColIn.Q, tup_ixOf I t]
  classical
  exact Finset.mem_union

theorem isSplitSet_sgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  intro X px I U L _ hL t PP h PP' h' hc
  have hc' : Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP PP' := fun c hm =>
    ⟨Formalism.DivisionValues.cO X.toD7.host.E c, (hc c (Formalism.DivisionValues.cO X.toD7.host.E c) rfl).1 hm, rfl⟩
  exact GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL.is t ((mem_sgL_iff X I U L hL t PP).1 h)
    ((mem_sgL_iff X I U L hL t PP').1 h') hc'

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
      (hu : (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp),
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr ⟨_, hu⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.RowChr.chr_eq_ch | exact GlobalTheory.Mem.R3.RowChr.chr_eq_ch | (intros; apply GlobalTheory.Mem.R3.RowChr.chr_eq_ch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalLevel_firstFactor_reads_component : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  first | exact @GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | exact GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | (intros; apply GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceSupport_level_standardCoordinates : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | exact GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff <;> assumption)
end

