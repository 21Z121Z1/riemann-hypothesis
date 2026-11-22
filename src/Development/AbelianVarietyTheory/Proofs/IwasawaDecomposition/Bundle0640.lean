import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.HTConst

theorem mem_of_pow_eq_one {K : Type} [Field K] (W : ValuationSubring K) {z : K} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) :
    z ∈ W := by
  rcases W.mem_or_inv_mem z with h1 | h1
  · exact h1
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact h)
    rw [e]
    exact pow_mem h1 _

theorem exists_intValuation_eq {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) {x : R}
    (hx : x ≠ 0) : ∃ n : ℕ, w.intValuation x = WithZero.exp (-(n : ℤ)) :=
  ⟨_, w.intValuation_if_neg hx⟩

theorem exists_mul_eq_mul {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) {x y : R}
    (hx : x ≠ 0) (h : w.intValuation x = w.intValuation y) :
    ∃ u v, u ∉ w.asIdeal ∧ v ∉ w.asIdeal ∧ u * y = v * x := by
  obtain ⟨n, hn⟩ := exists_intValuation_eq w hx
  have hx1 : x ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem x n).1 hn.le
  have hy1 : y ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem y n).1 (h ▸ hn.le)
  have hx2 : x ∉ w.asIdeal ^ (n + 1) := fun hc => by
    have := (w.intValuation_le_pow_iff_mem x (n + 1)).2 hc
    rw [hn, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hx1)
  have hAw : ¬ A ≤ w.asIdeal := fun hc => hx2 <| by
    have h1 : x ∈ w.asIdeal ^ n * A := hA ▸ Ideal.mem_span_singleton_self x
    rw [pow_succ]
    exact Ideal.mul_mono_right hc h1
  obtain ⟨u, huA, huw⟩ := SetLike.not_le_iff_exists.1 hAw
  have h2 : u * y ∈ Ideal.span {x} := by
    rw [hA, mul_comm u]
    exact Ideal.mul_mem_mul hy1 huA
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨u, v, huw, fun hc => ?_, hv.symm ▸ rfl⟩
  have hu1 : w.intValuation u = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 huw
  have h3 : w.intValuation v * w.intValuation x = w.intValuation x := by
    rw [← map_mul, hv, map_mul, hu1, _root_.one_mul, h]
  have hv1 : w.intValuation v = 1 := mul_right_cancel₀ (w.intValuation_ne_zero x hx) (by rw [h3, _root_.one_mul])
  exact (HeightOneSpectrum.intValuation_eq_one_iff.1 hv1) hc

theorem norm_of_isUnit {C : Type} [NormedField C] [IsUltrametricDist C] {t : ↥(intO C)} (h : IsUnit t) :
    ‖(t : C)‖ = 1 := by
  obtain ⟨s, hs⟩ := h.exists_right_inv
  have h1 : ‖(t : C)‖ ≤ 1 := t.2
  have h2 : ‖(s : C)‖ ≤ 1 := s.2
  have h3 : ‖(t : C)‖ * ‖(s : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, hs]
    simp
  nlinarith [norm_nonneg (t : C), norm_nonneg (s : C)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem exists_primitiveRoot (c : Coeff l) (W : ValuationSubring ℂ) {N : ℕ} (hN : N ∣ l.A) :
    ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N := by
  obtain ⟨d, hd⟩ := hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by
    rintro rfl
    exact l.A_pos.ne' (by simpa using hd))
  have hprim : IsPrimitiveRoot (zeta l.A ^ d) N :=
    (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow l.A_pos (by rw [hd, mul_comm])
  have hF : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hW : zeta l.A ^ d ∈ W := mem_of_pow_eq_one W hN0 hprim.pow_eq_one
  refine ⟨⟨⟨_, pow_mem hF d⟩, hW⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (c.F.val.toRingHom).comp (c.V W).subtype) hprim
    (c.F.val.toRingHom.injective.comp Subtype.val_injective)

theorem embed_mem (W : ValuationSubring ℂ) (τ : E →+* ℂ) (x : 𝓞 E) : τ (x : E) ∈ W := by
  have h1 : IsIntegral ℤ (τ (x : E)) := x.2.map τ.toIntAlgHom
  have h2 : IsIntegral W (τ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

theorem natCast_mem_maximalIdeal (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : (p : ↥(c.V W)) ∈ IsLocalRing.maximalIdeal ↥(c.V W) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : (p : ℂ) * (((y : c.F) : ℂ)) = 1 := by
    have := congrArg (fun t : ↥(c.V W) => (((t : c.F)) : ℂ)) hy
    simpa using this
  have h2 : ((y : c.F) : ℂ) = (p : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW
  rcases hW with h | h
  · exact hp.ne_zero (by exact_mod_cast h)
  · exact h (h2 ▸ y.2)

theorem exists_diffGen [IsGalois ℚ E] (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) :
    ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)),
      Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p) := by
  classical
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let j : 𝓞 E →+* ↥(c.V W) := (embK c τ).codRestrict (c.V W) fun x => embed_mem W τ x
  have hpm := natCast_mem_maximalIdeal c hp hW
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpc : (p : 𝓞 E) ∈ Ideal.comap j (IsLocalRing.maximalIdeal ↥(c.V W)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpm
  let w : HeightOneSpectrum (𝓞 E) := ⟨Ideal.comap j (IsLocalRing.maximalIdeal ↥(c.V W)), Ideal.comap_isPrime _ _,
    fun h => hp0 (by rw [h] at hpc; simpa using hpc)⟩
  have hpw : (p : 𝓞 E) ∈ w.asIdeal := hpc
  have hunit : ∀ u, u ∉ w.asIdeal → IsUnit (j u) := fun u hu => by
    by_contra hc
    exact hu ((IsLocalRing.mem_maximalIdeal _).2 hc)
  have hm := multiplicity_different_eq E hp w hpw
  set m := multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) with hmdef
  set e := Formalism.BasicNotions.eWL E w with hedef

  have hval : w.intValuation (p : 𝓞 E) = WithZero.exp (-(e : ℤ)) := by
    obtain ⟨n, hn⟩ := exists_intValuation_eq w hp0
    haveI := Fact.mk hp
    haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hpw
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    have he : e = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal := by
      rw [hedef, Formalism.BasicNotions.eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        (Ideal.span {(p : ℤ)}) w.asIdeal (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
    have h1 : (p : 𝓞 E) ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hn.le
    have h2 : (p : 𝓞 E) ∉ w.asIdeal ^ (n + 1) := fun hc => by
      have := (w.intValuation_le_pow_iff_mem _ (n + 1)).2 hc
      rw [hn, WithZero.exp_le_exp] at this
      push_cast at this
      omega
    have h3 := Ideal.count_normalizedFactors_eq (p := w.asIdeal) (x := Ideal.span {(p : 𝓞 E)}) (n := n)
      ((Ideal.span_singleton_le_iff_mem _).2 h1) (fun hc => h2 ((Ideal.span_singleton_le_iff_mem _).1 hc))
    rw [hn, he, h3]
  have he0 : e ≠ 0 := fun h0 => by
    have := (w.intValuation_lt_one_iff_mem _).2 hpw
    rw [hval, h0] at this
    simp at this
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hsame : w.intValuation (π ^ e) = w.intValuation (p : 𝓞 E) := by
    rw [map_pow, hπ, hval, ← WithZero.exp_nsmul]
    simp
  obtain ⟨u, v, hu, hv, huv⟩ := exists_mul_eq_mul w (pow_ne_zero e hπ0) hsame
  have huvj : j u * (p : ↥(c.V W)) = j v * (j π) ^ e := by
    have := congrArg j huv
    simpa using this
  have hdvd : (j π) ^ e ∣ (p : ↥(c.V W)) :=
    ((hunit u hu).dvd_mul_left).1 ⟨j v, by rw [huvj, mul_comm]⟩
  refine ⟨(j π) ^ m, ⟨m, Ideal.mem_span_singleton.2 ?_⟩, fun C φ => ?_⟩
  · refine dvd_trans ?_ (pow_dvd_pow_of_dvd hdvd m)
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero he0))
  · have hn : ‖((φ (j π) : ↥(intO ↥C.S)) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
      have h1 := congrArg (fun t => ‖((φ t : ↥(intO ↥C.S)) : ↥C.S)‖) huvj
      simp only [map_mul, map_pow, map_natCast, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, norm_mul,
        norm_pow] at h1
      rwa [norm_of_isUnit ((hunit u hu).map φ), norm_of_isUnit ((hunit v hv).map φ), _root_.one_mul, _root_.one_mul, C.norm_p,
        eq_comm] at h1
    have hlog : (e : ℝ) * Real.log ‖((φ (j π) : ↥(intO ↥C.S)) : ↥C.S)‖ = -Real.log p := by
      rw [← Real.log_pow, hn, Real.log_inv]
    rw [map_pow, Subring.coe_pow, norm_pow, Real.log_pow, hm]
    linear_combination (vDiff E p) * hlog

theorem const_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → (∀ N : ℕ, N ∣ l.A → ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N) ∧ (IsGalois ℚ E → ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p)) :=
  fun _ _ _ _ _ _ c _ _ hp hW => ⟨fun _ hN => exists_primitiveRoot c _ hN, fun _ => exists_diffGen c hp hW⟩

end GlobalTheory.HTConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem epi_spMap_field (Ω L : Type) [Field Ω] [Field L] (iL : Ω →+* L) : Epi (spMap iL) := by
  letI : Algebra Ω L := iL.toAlgebra
  have hf : Flat (spMap iL) := by
    rw [show spMap iL = Spec.map (CommRingCat.ofHom iL) from rfl]
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have hs : Surjective (spMap iL) := ⟨fun z =>
    ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem splitTors_of_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (x : Sp R ⟶ Y.X)
    (y : Sp (FractionRing R) ⟶ Xo.XF c), spMap (algebraMap R (FractionRing R)) ≫ x = y ≫ Y.j →
    ∀ N : ℕ, N ∣ l.A → GlobalTheory.LineNorm.SplitTors Y.t x N := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ x y hxy N hN Ω _ io w hw
  let L := AlgebraicClosure Ω
  let iL : Ω →+* L := algebraMap Ω L
  let xL : Sp L ⟶ Xo.XF c := spMap (iL.comp io) ≫ y
  obtain ⟨β', hβ⟩ : ∃ β' : KA l →+* L,
      xL ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β' :=
    ⟨(Spec.preimage (xL ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)).hom,
      (Spec.map_preimage _).symm⟩
  obtain ⟨-, I, -, hA, -⟩ := Y.oF.geom L xL β' hβ
  have hNpos : 0 < N := Nat.pos_of_dvd_of_pos hN l.A_pos
  obtain ⟨m, hm⟩ := hN
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; have := l.A_pos; omega
    · exact h
  have hU : xL ≫ Y.j = spMap iL ≫ spMap (io.comp (algebraMap R (FractionRing R))) ≫ x := by
    show (spMap (iL.comp io) ≫ y) ≫ Y.j = _
    rw [Category.assoc, ← hxy, ← spMap_comp' io iL, ← spMap_comp' (algebraMap R _) io]
    simp only [Category.assoc]
  let U : Over.mk (xL ≫ Y.j) ⟶ Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) :=
    Over.homMk (spMap iL) hU.symm
  let wL : Over.mk (xL ≫ Y.j) ⟶ Y.t.G := ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U w
  have hwL : wL ^ N = 1 := by
    show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U w ^ N = 1
    rw [← map_pow, hw, map_one]
  have h := Y.m.cart
  let P := pushHom h (Over.mk xL)
  let v : Over.mk xL ⟶ Y.oF.t.G :=
    Over.homMk (h.1.lift wL.left xL (Over.w wL)) (h.1.lift_snd _ _ _)
  have hvφ : v.left ≫ Y.m.φ = wL.left := h.1.lift_fst _ _ _
  have hPinj : Function.Injective P := by
    intro p q hpq
    have e : p.left ≫ Y.m.φ = q.left ≫ Y.m.φ := congrArg (fun V => V.left) hpq
    apply Over.OverMorphism.ext
    exact h.1.hom_ext e ((Over.w p).trans (Over.w q).symm)
  have hPv : P v = wL := Over.OverMorphism.ext hvφ
  have hvN : v ^ N = 1 := hPinj (by rw [map_pow, hPv, map_one]; exact hwL)
  obtain ⟨a, ha⟩ := (I.onto N hNpos v).1 hvN
  have hve : v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (SemiCartesianMonoidalCategory.toUnit (Over.mk xL)) (Y.oF.etaA a ^ m) := by
    rw [map_pow]
    show v = (SemiCartesianMonoidalCategory.toUnit (Over.mk xL) ≫ Y.oF.etaA a) ^ m
    rw [hA a, hm, I.tower N m hNpos hmpos a, ha]
  have e1 : v.left = xL ≫ (Y.oF.etaA a ^ m).left := by
    have e0 : (SemiCartesianMonoidalCategory.toUnit (Over.mk xL)).left = xL := by
      simpa using Over.w (SemiCartesianMonoidalCategory.toUnit (Over.mk xL))
    rw [hve]
    show (SemiCartesianMonoidalCategory.toUnit (Over.mk xL) ≫ (Y.oF.etaA a ^ m)).left = _
    rw [Over.comp_left, e0]
  refine ⟨y ≫ (Y.oF.etaA a ^ m).left ≫ Y.m.φ, ?_⟩
  haveI := epi_spMap_field Ω L iL
  rw [← cancel_epi (spMap iL)]
  have e2 : wL.left = spMap iL ≫ w.left := rfl
  rw [← e2, ← hvφ, e1]
  show _ = ((spMap (iL.comp io) ≫ y) ≫ _) ≫ _
  rw [← spMap_comp' io iL]
  simp only [Category.assoc]

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms
section
open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Covol

open Matrix

theorem sum_prod_mul_minor {C : Type} [CommRing C] {g m k : ℕ} (h : Fin k → Fin g → C) (a : Fin m → Fin g → C)
    (hk : k ≤ m) :
    ∑ s : Fin k → Fin g, (∏ i, h i (s i)) * minor a hk s =
      (Matrix.of fun l i => ∑ t, h i t * a (Fin.castLE hk l) t).det := by
  unfold minor
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_pivot {L : Type} [Field L] (W : ValuationSubring L) {J : Type} [Fintype J] {r : ℕ}
    (g : Matrix J (Fin r) L) (hg : LinearIndependent L gᵀ) :
    ∃ (ι : Fin r → J) (u : Matrix J (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
      (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
      (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  let e := Fintype.equivFin J
  have hg' : LinearIndependent L (g.submatrix e.symm id)ᵀ :=
    hg.map' (LinearEquiv.funCongrLeft L L e.symm).toLinearMap (LinearEquiv.ker _)
  obtain ⟨ι, u, b, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_integral_pivot_decomposition L W _ _ _ hg'
  refine ⟨fun i => e.symm (ι i), u.submatrix e id, b, fun _ _ => h1 _ _, fun i j hij => ?_, fun i => ?_, h4, h5, ?_⟩
  · simpa using h2 i j hij
  · simpa using h3 i
  · ext j l
    have := congrFun (congrFun h6 (e j)) l
    simpa [Matrix.mul_apply] using this

theorem det_eq {C : Type} [Field C] {J : Type} {n : ℕ}
    (u : Matrix J (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (hb : b.BlockTriangular id)
    {k : ℕ} (hk : k ≤ n) (σ : Fin k → J) :
    ((u * b).submatrix σ (Fin.castLE hk)).det =
      (u.submatrix σ (Fin.castLE hk)).det * ∏ l : Fin k, b (Fin.castLE hk l) (Fin.castLE hk l) := by
  have h1 : (u * b).submatrix σ (Fin.castLE hk) =
      u.submatrix σ (Fin.castLE hk) * b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext l' l
    rw [submatrix_apply, mul_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
    intro j hj
    have : b j (Fin.castLE hk l) = 0 := by
      apply hb
      by_contra hlt
      have hle : (j : ℕ) ≤ l := Fin.le_def.mp (not_lt.mp hlt)
      exact hj ⟨⟨j, lt_of_le_of_lt hle l.2⟩, rfl⟩
    rw [this, mul_zero]
  have h3 : (b.submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id := fun i j hij => hb hij
  rw [h1, det_mul, Matrix.det_of_isUpperTriangular h3]
  rfl

theorem mem_of_mulVec {C : Type} [Field C] (W : ValuationSubring C) {J : Type} {n : ℕ} (ι : Fin n → J)
    (u : Matrix J (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (y : Fin n → C)
    (hy : ∀ s, (u *ᵥ y) s ∈ W) (i : Fin n) : y i ∈ W :=
  GlobalTheory.FlagEmb.GradedNorm.mem_of_mulVec W id (u.submatrix ι id) (fun _ _ => huW _ _) hu0 hu1 y
    (fun s => hy (ι s)) i

theorem prod_grNorm_eq_iSup_minor : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (g : ℕ) (J : Type) [Fintype J] (h : J → Fin g → C), (∀ c : Fin g → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0) → ∀ (m : ℕ) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ (N : Fin m → ℝ), (∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) → (∀ l, 0 < N l) ∧ ∀ (k : ℕ) (hk : k ≤ m), ∏ l : Fin k, N (Fin.castLE hk l) = ⨆ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ := by
  intro C _ _ g J _ h hh m a ha N hN
  let W : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  let G : Matrix J (Fin m) C := Matrix.of fun j l => ∑ t, h j t * a l t
  have hli : LinearIndependent C Gᵀ := by
    have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ :=
      LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j
    exact ha.map' _ hker
  obtain ⟨ι, u, b, huW, hu0, hu1, hb, hbd, hc⟩ := exists_pivot W G hli
  have hsum : ∀ (cf : Fin m → C) (j : J), ∑ i, h j i * ∑ l', cf l' * a l' i = (u *ᵥ (b *ᵥ cf)) j := fun cf j => by
    rw [mulVec_mulVec, ← hc]
    simp only [G, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hbdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd i).isUnit
  have hNb : ∀ i, N i = ‖b i i‖ := by
    intro i
    have hdiag : ∀ cf : Fin m → C, (∀ k, i < k → cf k = 0) → (b *ᵥ cf) i = b i i * cf i := fun cf hcf => by
      rw [mulVec, dotProduct]
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hb h, zero_mul]
      · rw [hcf j h, mul_zero]
    rw [hN]
    apply IsLeast.csInf_eq
    constructor
    · letI := b.invertibleOfIsUnitDet hbdet
      have hinv : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
      have hz : ∀ k, i < k → (b⁻¹ *ᵥ Pi.single i 1 : Fin m → C) k = 0 := fun k hk => by
        rw [mulVec_single_one]
        exact hinv hk
      have hbb : b *ᵥ (b⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, mul_nonsing_inv _ hbdet, one_mulVec]
      have h1 := hdiag _ hz
      rw [hbb, Pi.single_eq_same] at h1
      refine ⟨b⁻¹ *ᵥ Pi.single i 1, right_ne_zero_of_mul (h1 ▸ one_ne_zero), hz, fun s => ?_, ?_⟩
      · rw [hsum, hbb, mulVec_single_one]
        exact (hW _).1 (huW _ _)
      · rw [eq_inv_of_mul_eq_one_left h1.symm, norm_inv]
    · rintro r ⟨cf, hcf, hz, hint, rfl⟩
      have h1 := (hW _).1 (mem_of_mulVec W ι u huW hu0 hu1 (b *ᵥ cf)
        (fun s => (hW _).2 (hsum cf s ▸ hint s)) i)
      rw [hdiag cf hz, norm_mul] at h1
      rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hcf)]
      exact h1
  refine ⟨fun l => hNb l ▸ norm_pos_iff.2 (hbd l), fun k hk => ?_⟩
  have hdet : ∀ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ =
      ‖(u.submatrix σ (Fin.castLE hk)).det‖ * ∏ l : Fin k, N (Fin.castLE hk l) := fun σ => by
    rw [sum_prod_mul_minor (fun i => h (σ i)) a hk, ← det_transpose]
    change ‖(G.submatrix σ (Fin.castLE hk)).det‖ = _
    rw [hc, det_eq u b hb hk, norm_mul, norm_prod]
    simp only [hNb]
  symm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨ι ∘ Fin.castLE hk, ?_⟩
    have hMt : (u.submatrix (ι ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
      fun i j hij => hu0 _ _ hij
    beta_reduce
    rw [hdet, Matrix.det_of_isLowerTriangular _ hMt]
    simp [hu1]
  · rintro _ ⟨σ, rfl⟩
    beta_reduce
    rw [hdet]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => hNb _ ▸ norm_nonneg _)
      ((hW _).1 (GlobalTheory.FlagEmb.GradedNorm.det_mem W _ fun _ _ => huW _ _))

end GlobalTheory.LineNorm.Covol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumRankOneIntegralRescaling
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem scaleDecomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N)
    (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) →
    ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧
      (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧
      (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) =
        ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  intro E _ _ _ N X d ξ t ht
  choose a ha hmem using fun j => GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (ξ j)
  obtain ⟨b, hb, hint⟩ := GlobalTheory.T.exists_common_denominator_isIntegral E d (fun j => t j / ((a j : ℕ) : E) ^ 2)
  have ha0 : ∀ j, ((a j : ℕ) : E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (ha j).ne'
  refine ⟨X.m * b, fun j => ((a j : ℕ) : E) • ξ j, fun j => (b : E) * (t j / ((a j : ℕ) : E) ^ 2),
    Nat.mul_pos X.m_pos hb, hmem, fun j => ⟨_, rfl⟩, ?_, hint, ?_⟩
  · intro j
    rw [cc_mul, div_eq_mul_inv, cc_mul, cc_inv, cc_pow, cc_natCast, cc_natCast, ht, ← div_eq_mul_inv]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rk1_smul_left, rk1_smul_right, cc_natCast, smul_smul, smul_smul, smul_smul]
    congr 1
    have := ha0 j
    push_cast
    field_simp

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponentStatement
section
open NumberField IsDedekindDomain Formalism.L2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_heckeCharacter_split_place_local_component : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  first | exact @GlobalTheory.HeckeSplitComp.main | exact GlobalTheory.HeckeSplitComp.main | (intros; apply GlobalTheory.HeckeSplitComp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenActionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_eigen_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X), (∀ (n : ℕ) (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R), (∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j) → IsCombAtG t x u cf w → w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w) ∧ ∀ (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult) (y : CellVar Dw.mult → R), IsFrame t f x e → (∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) → IsFrame t f x u := by
  first | exact @GlobalTheory.FlagEmb.eig_comb_and_frame_cell | exact GlobalTheory.FlagEmb.eig_comb_and_frame_cell | (intros; apply GlobalTheory.FlagEmb.eig_comb_and_frame_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  first | exact @GlobalTheory.ShFam.TieUp.main | exact GlobalTheory.ShFam.TieUp.main | (intros; apply GlobalTheory.ShFam.TieUp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_character_cocycle_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (x : Sp R ⟶ X) (q : ℕ) (B : Type) [CommRing B] [Algebra R B] (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), IsFinPart t x q u → ∀ κ : (B →ₐ[R] R) → Rˣ, (∀ (σ σ' σ'' : B →ₐ[R] R) (w w' : Over.mk (spMap (RingHom.id R) ≫ x) ⟶ t.G), spMap σ.toRingHom ≫ u.left = w.left → spMap σ'.toRingHom ≫ u.left = w'.left → spMap σ''.toRingHom ≫ u.left = (w * w').left → κ σ'' = κ σ * κ σ') → ∃ b : Bˣ, (∀ σ : B →ₐ[R] R, σ (b : B) = (κ σ : R)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (β β' β'' : B →+* S), β.comp (algebraMap R B) = φ → β'.comp (algebraMap R B) = φ → β''.comp (algebraMap R B) = φ → spMap β ≫ u.left = w.left → spMap β' ≫ u.left = w'.left → spMap β'' ≫ u.left = (w * w').left → β'' (b : B) = β (b : B) * β' (b : B) := by
  first | exact @GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart | exact GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart | (intros; apply GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart <;> assumption)
end

