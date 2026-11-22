import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalCharacterIsUnramifiedOfHeckeUnram
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinUnram

open GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem off_idl (p : SplitPt D k) (a : kˣ) : (1 - p.e) * ((idl p a : (AE D)ˣ) : AE D) = 1 - p.e := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination (-1 : AE D) * ha + he

theorem e_mul_idl (p : SplitPt D k) (a : kˣ) : p.e * ((idl p a : (AE D)ˣ) : AE D) = p.sec a := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination ha - he

theorem map_e_eq_zero (p : SplitPt D k) {R : Type} [CommRing R] (f : AE D →+* R) (h : f (p.e + cA D p.e) = 0) :
    f p.e = 0 := by
  have h1 : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, p.split.1, p.split.2.1, add_zero]
  rw [h1, RingHom.map_mul, h, mul_zero]

theorem infPart_e (p : SplitPt D k) : infPart D p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, -⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem compAt_e (p : SplitPt D k) {w : Pl D} (hw : w ≠ p.v) : compAt D w p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, h0⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [h0 w hw]
  exact TensorProduct.zero_tmul _ _

theorem idl_int (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) :
    finPart D ((idl p a : (AE D)ˣ) : AE D) ∈ intAE D := by
  rw [idl_val, RingHom.map_add, RingHom.map_sub, RingHom.map_one]
  refine add_mem ((p.int_iff _).1 ha) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)) ?_)
  rw [← sec_one]
  exact (p.int_iff 1).1 (one_mem _)

theorem absFin_idl (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) (ha' : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k]) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have key : ∀ b : kˣ, (b : k) ∈ 𝒪[k] →
      Valued.v ((Units.map π.toMonoidHom (idl p b) : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := fun b hb =>
    GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 (by rw [e_mul_idl]; exact (p.int_iff _).1 hb))
  have a1 := key a ha
  have a2 := key _ ha'
  rw [GlobalTheory.SplitLinear.absFin_split D p.e v π p.split hπ _ (off_idl p a)]
  rw [MonoidHom.map_inv, MonoidHom.map_inv] at a2
  generalize Units.map π.toMonoidHom (idl p a) = y at a1 a2 ⊢
  have hne : Valued.v (y : Fv D.host.F v) ≠ 0 := by simp
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at a2
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, le_antisymm a1 a2]

theorem lam_unram : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (GlobalTheory.SplitLinAt.lam p χ r) := by
  intro D k _ _ _ _ p χ r hχ a ha
  have h1 : (a : k) ∈ 𝒪[k] := ha.le
  have h2 : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    change valuation k ((a⁻¹ : kˣ) : k) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  have h3 : χ (idl p a) = 1 :=
    hχ _ (GlobalTheory.SplitLinear.off_norm'' _ (infPart_e p) (off_idl p a))
      (fun w hw => GlobalTheory.SplitLinear.off_norm'' (compAt D w) (compAt_e p hw) (off_idl p a)) (idl_int p h1)
      (by rw [← MonoidHom.map_inv]; exact idl_int p h2)
  refine Units.ext ?_
  rw [lam_val, h3, absFin_idl p h1 h2, Real.one_rpow]
  simp

end GlobalTheory.SplitLinUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmField
section
noncomputable section

namespace GlobalTheory.StableRange

open IsDedekindDomain NumberField

theorem exists_inv_mod_maximal {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (b : S) :
    ∃ y : S, ∀ m : Ideal S, m.IsMaximal → b ∈ m ∨ 1 - b * y ∈ m := by
  let I : Ideal S := (Ideal.jacobson (⊥ : Ideal B)).map (algebraMap B S)
  have hI : ∀ m : Ideal S, m.IsMaximal → I ≤ m := by
    intro m hm
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap B S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    exact sInf_le ⟨bot_le, this⟩
  have hp : ∀ p : Ideal S, p.IsPrime → I ≤ p → p.IsMaximal := by
    intro p hp hIp
    rw [Ideal.map_le_iff_le_comap] at hIp
    have hq : (p.comap (algebraMap B S)).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (p.comap (algebraMap B S)).IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨(Ideal.ne_top_iff_one _).1 hq.ne_top, fun J x hJ hx hxJ => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have h1 : x * (1 - x * y) ∈ p.comap (algebraMap B S) :=
        hIp (Ideal.mem_jacobson_bot.2 hy)
      have h2 := (hq.mem_or_mem h1).resolve_left hx
      have := J.add_mem (hJ h2) (J.mul_mem_right y hxJ)
      simpa using this
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B) p hmax
  let M : Submonoid S :=
    { carrier := {s | ∃ (n : ℕ) (y : S), s = b ^ n * (1 - b * y)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, y, rfl⟩ ⟨k, w, rfl⟩
        exact ⟨n + k, y + w - b * y * w, by ring⟩ }
  by_cases hd : Disjoint (I : Set S) (M : Set S)
  · exfalso
    obtain ⟨p, hpp, hIp, hdis⟩ := Ideal.exists_le_prime_disjoint I M hd
    have hm := hp p hpp hIp
    have hb : b ∉ p := fun h => Set.disjoint_left.1 hdis h ⟨1, 0, by simp⟩
    obtain ⟨y, i, hi, hy⟩ := hm.exists_inv hb
    refine Set.disjoint_left.1 hdis hi ⟨0, y, ?_⟩
    rw [← hy]; ring
  · obtain ⟨s, hsI, n, y, rfl⟩ := Set.not_disjoint_iff.1 hd
    refine ⟨y, fun m hm => ?_⟩
    rcases hm.isPrime.mem_or_mem (hI m hm hsI) with h | h
    · exact Or.inl (hm.isPrime.mem_of_pow_mem n h)
    · exact Or.inr h

theorem stable_of_isIntegral {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hB : ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1)) (a b : S)
    (h : IsCoprime a b) : ∃ t : S, IsUnit (a + t * b) := by
  obtain ⟨y, hy⟩ := exists_inv_mod_maximal hB b
  obtain ⟨u, w, huw⟩ := h
  refine ⟨y * (1 - a), ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := a + y * (1 - a) * b) hn
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hy m hm with hb | hb
  · have e : (1 : S) = u * (a + y * (1 - a) * b) + (w - u * (y * (1 - a))) * b := by
      linear_combination -huw
    rw [e]
    exact m.add_mem (m.mul_mem_left _ hmem) (m.mul_mem_left _ hb)
  · have e : (1 : S) = (a + y * (1 - a) * b) + (1 - a) * (1 - b * y) := by ring
    rw [e]
    exact m.add_mem hmem (m.mul_mem_left _ hb)

theorem stable_of_subrings {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R]
    (hA : ∀ s : Finset A, ∃ B : Subring A, (s : Set A) ⊆ B ∧
      ∀ x : B, ∃ y : B, ∀ z : B, IsUnit (x * (1 - x * y) * z + 1))
    (a b : R) (h : IsCoprime a b) : ∃ t : R, IsUnit (a + t * b) := by
  classical
  obtain ⟨u, w, huw⟩ := h
  choose p hpm hp using fun r : R => (Algebra.IsIntegral.isIntegral (R := A) r)
  obtain ⟨B, hs, hB⟩ := hA ((p a).coeffs ∪ (p b).coeffs ∪ (p u).coeffs ∪ (p w).coeffs)
  have key : ∀ r : R, ((p r).coeffs : Set A) ⊆ B → IsIntegral B r := by
    intro r hr
    refine ⟨(p r).toSubring B hr, (Polynomial.monic_toSubring _ _ hr).2 (hpm r), ?_⟩
    have e : algebraMap B R = (algebraMap A R).comp B.subtype := rfl
    rw [e, ← Polynomial.eval₂_map, Polynomial.map_toSubring]
    exact hp r
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  obtain ⟨t, ht⟩ := stable_of_isIntegral (S := integralClosure B R) hB ⟨a, key a h1⟩ ⟨b, key b h2⟩
    ⟨⟨u, key u h3⟩, ⟨w, key w h4⟩, Subtype.ext huw⟩
  exact ⟨t, ht.map (integralClosure B R).val⟩

variable (K : Type*) [Field K] [NumberField K]

def intOutside (T : Set (HeightOneSpectrum (𝓞 K))) : Subring (AdeleRing (𝓞 K) K) where
  carrier := {x | ∀ v ∉ T, x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)
  one_mem' v _ := one_mem (v.adicCompletionIntegers K)
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

def mkAdele {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (f : ∀ w : InfinitePlace K, w.Completion) (g : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hg : ∀ v ∉ T, g v ∈ v.adicCompletionIntegers K) : intOutside K T :=
  ⟨(f, ⟨g, hT.subset fun v hv => by
    by_contra h
    exact hv (hg v h)⟩), hg⟩

theorem isUnit_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (x : intOutside K T)
    (h1 : ∀ w, x.1.1 w ≠ 0) (h2 : ∀ v, x.1.2 v ≠ 0) (h3 : ∀ v ∉ T, Valued.v (x.1.2 v) = 1) :
    IsUnit x := by
  refine IsUnit.of_mul_eq_one (mkAdele K hT (fun w => (x.1.1 w)⁻¹) (fun v => (x.1.2 v)⁻¹)
    fun v hv => ?_) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h3 v hv, inv_one]
  · refine Subtype.ext (Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_))
    · exact mul_inv_cancel₀ (h1 w)
    · exact mul_inv_cancel₀ (h2 v)

theorem mul_one_sub_mul_inv {L : Type*} [Field L] (x : L) : x * (1 - x * x⁻¹) = 0 := by
  by_cases h : x = 0
  · simp [h]
  · simp [h]

open Classical in
theorem regular_intOutside {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (x : intOutside K T) :
    ∃ y : intOutside K T, ∀ z : intOutside K T, IsUnit (x * (1 - x * y) * z + 1) := by
  refine ⟨mkAdele K hT (fun w => (x.1.1 w)⁻¹)
    (fun v => if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0) fun v hv => ?_, fun z => ?_⟩
  · split_ifs with h
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h.resolve_left hv, inv_one]
    · exact zero_mem _
  · have hv : ∀ v, Valued.v (x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1) = 1 := by
      intro v
      split_ifs with h
      · rw [mul_one_sub_mul_inv]; simp
      · obtain ⟨hT', h1⟩ := not_or.1 h
        have hx : Valued.v (x.1.2 v) ≤ 1 := x.2 v hT'
        have hz : Valued.v (z.1.2 v) ≤ 1 := z.2 v hT'
        rw [mul_zero, sub_zero, mul_one, add_comm]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        exact (mul_le_of_le_one_right' hz).trans_lt (lt_of_le_of_ne hx h1)
    refine isUnit_intOutside K hT _ (fun w => ?_) (fun v => ?_) (fun v _ => hv v)
    · change x.1.1 w * (1 - x.1.1 w * (x.1.1 w)⁻¹) * z.1.1 w + 1 ≠ 0
      rw [mul_one_sub_mul_inv]; simp
    · intro h0
      have h1 := hv v
      have h2 : x.1.2 v * (1 - x.1.2 v *
        (if v ∈ T ∨ Valued.v (x.1.2 v) = 1 then (x.1.2 v)⁻¹ else 0)) * z.1.2 v + 1 = 0 := h0
      rw [h2] at h1
      simp at h1

theorem stable_adele {R : Type*} [CommRing R] [Algebra (AdeleRing (𝓞 K) K) R]
    [Algebra.IsIntegral (AdeleRing (𝓞 K) K) R] (a b : R) (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  refine stable_of_subrings (A := AdeleRing (𝓞 K) K) (fun s => ?_) a b h
  have hT : (⋃ x ∈ (s : Set (AdeleRing (𝓞 K) K)),
      {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}).Finite :=
    s.finite_toSet.biUnion fun x _ => x.2.2
  refine ⟨intOutside K _, fun x hx v hv => ?_, regular_intOutside K hT⟩
  by_contra h
  exact hv (Set.mem_biUnion hx h)

end GlobalTheory.StableRange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.StableRange.adeles_stableRange_one :
    ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) :=
  fun D a b h => GlobalTheory.StableRange.stable_adele D.host.F a b h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BoxSlice

open GlobalTheory.MixModel.OrthDec

variable {D : D7} {S A B : HSp D} (d : GlobalTheory.MixModel.OrthDec S A B)

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem resS_symm_left (T : HSp D) (u : WO A T) :
    (d.resS T).symm (u, 0) = GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA u := by
  rw [resS_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem isThetaFunO_slice_left {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO B T) : IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v)) where
  quasi γ u := by
    have e0 : (d.resS T).symm (ratW T A γ, 0) = ratW T S (γ * d.qA) := by
      rw [resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW T A γ + u, v) : WO A T × WO B T) = (ratW T A γ, (0 : WO B T)) + (u, v) := by simp
    show f ((d.resS T).symm (ratW T A γ + u, v)) = ψ (-(symplOH A T (ratW T A γ) u)) * f ((d.resS T).symm (u, v))
    rw [e, map_add, e0, hf.quasi, ← e0, d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (k _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resS T).symm (w, v))
    rw [← resS_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero, d.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  smooth k L hL h0 w := by
    have e : ∀ t, (d.resS T).symm (w + L t, v) =
        (d.resS T).symm (w, v) + ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resS_symm_left, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth k ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _

theorem isThetaFunO_slice_right {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO A T) : IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v)) := by
  have h := isThetaFunO_slice_left d.symm hf u
  have e : ∀ v, (d.symm.resS T).symm (v, u) = (d.resS T).symm (u, v) := fun v => by
    rw [resS_symm_apply, resS_symm_apply, add_comm]; rfl
  simp only [e] at h
  exact h

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  intro D ψ _ S A B T o
  refine ⟨fun fA fB hA hB => o.isThetaFunO_boxS hA hB, fun fA fB => o.boxS_zero T fA fB,
    fun fA fB => ⟨fun u => ?_, fun v => ?_⟩, fun f hf => ⟨fun v => isThetaFunO_slice_left o hf v,
      fun u => isThetaFunO_slice_right o hf u⟩⟩
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']

end GlobalTheory.BoxSlice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionalInvarianceProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open GlobalTheory.PlaceModel

namespace GlobalTheory.ProdForm

def iterForm {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
  ℓA ∘ₗ LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))

theorem iterForm_boxS {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) (fA : WO A T → ℂ) (fB : WO B T → ℂ) :
    iterForm o ℓA ℓB (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  have h : (LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b)))
      (o.boxS T fA fB) = ℓB fB • fA := by
    funext a
    have : (LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))) (o.boxS T fA fB) = fA a • fB := by
      funext b
      simp [LinearMap.funLeft_apply, OrthDec.boxS]
    simp [this, mul_comm]
  rw [iterForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

theorem exists_product_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  intro D ψ hψ S A B T o e hs ℓA ℓB hA hB
  classical
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]

  have hresA : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).1 i j = (o.resS T u).1 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  have hresB : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).2 i j = (o.resS T u).2 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  set l0 := iterForm o ℓA ℓB with hl0
  let gen : Set (WO S T → ℂ) := {f | ∃ fA fB, IsThetaFunO ψ A T fA ∧ IsThetaFunO ψ B T fB ∧ f = o.boxS T fA fB}
  let P : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ gen

  have hPst : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, heisL S T ψ u p ∈ P := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfA (o.resS T u).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfB (o.resS T u).2, ?_⟩
      exact o.heisO_boxS ψ T fA fB u
    | zero => rw [map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact P.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact P.smul_mem c ha
  have hl0P : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, l0 (heisL S T ψ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      change l0 (heisO ψ S T u (o.boxS T fA fB)) = _
      rw [o.heisO_boxS ψ T fA fB u, hl0, iterForm_boxS, iterForm_boxS, hA _ (hresA u hu) fA hfA,
        hB _ (hresB u hu) fB hfB]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]

  let K : Submodule ℂ (WO S T → ℂ) :=
    Submodule.span ℂ {m | ∃ u ∈ half S T (cA D e), ∃ g ∈ {g | IsThetaFunO ψ S T g}, m = heisL S T ψ u g - g}
  have hsm : ∀ u ∈ half S T (cA D e), ∀ g ∈ {g | IsThetaFunO ψ S T g}, ∃ k : ℕ, 0 < k ∧ heisL S T ψ (k • u) g = g := by
    intro u hu g hg
    obtain ⟨U, hU, h⟩ := (show IsThetaFunO ψ S T g from hg).level
    obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
    exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero (heisL_half S T ψ c2)
      (GlobalTheory.SplitScalar.heisO_zero ψ S T) hsm hmK
    have h1 : l0 (∑ j ∈ s, heisL S T ψ (y j) m) = (s.card : ℂ) * l0 m := by
      rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc

  let fP : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : WO S T → ℂ) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : WO S T → ℂ) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu f hf => ?_, fun fA fB hfA hfB => ?_⟩
  · have huY : u ∈ half S T (cA D e) := (isHalf_iff S T).1 hu
    have hk : heisO ψ S T u f - f ∈ K := Submodule.subset_span ⟨u, huY, f, hf, rfl⟩
    have hz : heisO ψ S T u f - f ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (heisO ψ S T u f - f) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp : o.boxS T fA fB ∈ P := Submodule.subset_span ⟨fA, fB, hfA, hfB, rfl⟩
    have hz : o.boxS T fA fB ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 (o.boxS T fA fB) + 0 = _
    rw [add_zero, hl0, iterForm_boxS]

end GlobalTheory.ProdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  first | exact @GlobalTheory.LocChar.weil_char_split | exact GlobalTheory.LocChar.weil_char_split | (intros; apply GlobalTheory.LocChar.weil_char_split <;> assumption)
end

