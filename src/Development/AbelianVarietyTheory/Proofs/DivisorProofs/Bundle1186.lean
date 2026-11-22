import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open MvPolynomial

theorem exists_weightedMonomialPlace : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z wt hN hm hz hw0 hw
  haveI := hN
  have hz0 : (z 0 : L) ≠ 0 := by
    intro h
    have h1 : z 0 = 0 := Subtype.ext h
    have := GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz (wt 0) (X 0) (isWeightedHomogeneous_X Q wt 0)
      (by simp [h1]) (Finsupp.single 0 1)
    rw [coeff_X, if_pos rfl, hm] at this
    exact (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  set u : Fin r → L := fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ with hu
  have key0 : ∀ P : MvPolynomial (Fin r) Q, eval₂ Q.subtype u P = 0 →
      ∀ α, P.coeff α ∈ IsLocalRing.maximalIdeal Q := by
    intro P hP α
    obtain ⟨N, F, hF, hFe, hc⟩ := GlobalTheory.T.exists_weightedHomogeneous_homogenisation Q r z wt hw0 hz0 P
    obtain ⟨β, hβ⟩ := hc α
    rw [← hβ, ← hm]
    refine GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz N F hF ?_ β
    apply Subtype.ext
    rw [hFe, hP, mul_zero]
    rfl
  set e : MvPolynomial (Fin r) Q →+* L := eval₂Hom Q.subtype u with he
  set A : Subring L := e.range with hA
  set eA : MvPolynomial (Fin r) Q →+* A := e.rangeRestrict with heA
  have heA_surj : Function.Surjective eA := e.rangeRestrict_surjective
  have heA_val : ∀ P, ((eA P : A) : L) = e P := fun P => rfl
  have hQA : ∀ q ∈ Q, q ∈ A := fun q hq => ⟨C ⟨q, hq⟩, by simp [he]⟩
  have huA : ∀ i, u i ∈ A := fun i => ⟨X i, by simp [he]⟩
  let t : A := ⟨z 0, hQA _ (z 0).2⟩
  have hzA : ∀ j, ∃ a : A, ((z j : Q) : L) = (z 0 : L) * a := by
    intro j
    refine Fin.cases ⟨1, by simp⟩ (fun i => ?_) j
    refine ⟨⟨(z 0 : L) ^ (wt i.succ - 1) * u i, A.mul_mem (A.pow_mem (hQA _ (z 0).2) _) (huA i)⟩, ?_⟩
    show ((z i.succ : Q) : L) = (z 0 : L) * ((z 0 : L) ^ (wt i.succ - 1) * ((z i.succ : L) / (z 0 : L) ^ wt i.succ))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hw i.succ), mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
  have hmA : Ideal.map (eA.comp C) (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {t} := by
    rw [Ideal.map_le_iff_le_comap, ← hm, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hzA j
    show eA (C (z j)) ∈ Ideal.span {t}
    rw [Ideal.mem_span_singleton']
    exact ⟨a, Subtype.ext (by rw [heA_val]; simp [he, ha, mul_comm, t])⟩
  have hspan : Ideal.span {t} = Ideal.map eA (Ideal.map C (IsLocalRing.maximalIdeal Q)) := by
    rw [Ideal.map_map]
    refine le_antisymm ?_ hmA
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : t = (eA.comp C) (z 0) := Subtype.ext (by rw [RingHom.comp_apply, heA_val]; simp [he, t])
    rw [SetLike.mem_coe, this]
    exact Ideal.mem_map_of_mem _ (by rw [← hm]; exact Ideal.subset_span ⟨0, rfl⟩)
  have hker : RingHom.ker eA ≤ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [MvPolynomial.mem_map_C_iff]
    refine key0 P ?_
    have := congrArg Subtype.val ((RingHom.mem_ker).mp hP)
    simpa [heA_val, he] using this
  have hprimeC : (Ideal.map (C : Q →+* MvPolynomial (Fin r) Q) (IsLocalRing.maximalIdeal Q)).IsPrime := by
    have := MvPolynomial.ker_map (σ := Fin r) (IsLocalRing.residue Q)
    rw [IsLocalRing.ker_residue] at this
    rw [← this]
    exact RingHom.ker_isPrime _
  have hprime : (Ideal.span {t}).IsPrime := by
    rw [hspan]
    exact Ideal.map_isPrime_of_surjective heA_surj hker
  have key1 : ∀ P : MvPolynomial (Fin r) Q, eA P ∈ Ideal.span {t} →
      P ∈ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [hspan] at hP
    obtain ⟨x, hx, hxP⟩ := (Ideal.mem_map_iff_of_surjective eA heA_surj).mp hP
    have : P - x ∈ RingHom.ker eA := by rw [RingHom.mem_ker, map_sub, hxP, sub_self]
    simpa using Ideal.add_mem _ (hker this) hx
  have hNA : IsNoetherianRing A := isNoetherianRing_of_surjective _ _ eA heA_surj
  have hfracA : ∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
    intro f
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hQ.frac f
    exact ⟨a, hQA a ha, b, hQA b hb, hb0, hab⟩
  obtain ⟨V, hAV, hdvr, hirr, hunit, hfrV, hess⟩ :=
    GlobalTheory.T.isDVR_of_principal_prime_localization A t hNA hz0 hprime hfracA
  have hQAf : (Q.subtype.codRestrict A fun q => hQA _ q.2).FiniteType := by
    have h1 : (Q.subtype.codRestrict A fun q => hQA _ q.2) = eA.comp C := by
      ext q; simp [heA_val, he]
    rw [h1]
    exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance) heA_surj
  have hconst : ∀ a, c a ∈ V := fun a => hAV _ (hQA _ (hQ.const_mem a))
  have hessV : (c.codRestrict V hconst).EssFiniteType := by
    have h := (hQ.essFiniteType.comp hQAf.essFiniteType).comp hess
    exact h
  let P0 : Place c := ⟨V, hconst, hdvr, hessV⟩
  have hC : P0.Contains Q := fun f hf => hAV _ (hQA _ hf)
  let uV : Fin r → P0.ring := fun i => ⟨u i, hAV _ (huA i)⟩
  have hev : ∀ P : MvPolynomial (Fin r) Q,
      ((MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P : P0.ring) : L) =
        e P := by
    intro P
    exact MvPolynomial.eval₂_comp_left (P0.ring.subtype)
      (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P
  refine ⟨P0, hC, uV, fun i => ?_, ?_, fun q hq => ?_, fun P hP => ?_, fun f => ?_⟩
  · exact div_mul_cancel₀ _ (pow_ne_zero _ hz0)
  · exact hirr
  · obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton').mp (hmA (Ideal.mem_map_of_mem _ hq))
    have hmt : (⟨(t : L), hAV _ t.2⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit
    have : (⟨(q : L), hC _ q.2⟩ : P0.ring) = ⟨(a : L), hAV _ a.2⟩ * ⟨(t : L), hAV _ t.2⟩ :=
      Subtype.ext (by have := congrArg Subtype.val ha; simpa [heA_val, he] using this.symm)
    rw [this]
    exact Ideal.mul_mem_left _ _ hmt
  · have hs : eA P ∉ Ideal.span {t} := fun h => by
      obtain ⟨α, hα⟩ := hP
      exact hα ((MvPolynomial.mem_map_C_iff.mp (key1 P h)) α)
    have := hunit _ hs
    convert this using 1
    exact Subtype.ext (hev P)
  · obtain ⟨a, s, hs, hfs⟩ := hfrV f
    obtain ⟨P, rfl⟩ := heA_surj a
    obtain ⟨R, rfl⟩ := heA_surj s
    refine ⟨P, R, ?_, Subtype.ext ?_⟩
    · convert hunit _ hs using 1
      exact Subtype.ext (hev R)
    · calc ((f * MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV R : P0.ring) : L)
          = (f : L) * e R := by rw [← hev R]; rfl
        _ = e P := hfs
        _ = _ := (hev P).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegular
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  intro p _ G β hβ y₀ s hy hsep hdeg S
  classical
  set Ec : Subalgebra ℚ G.C := Subalgebra.centralizer ℚ ({(y₀ : G.C)} : Set G.C) with hEc
  have memE : ∀ x : G.C, x ∈ Ec ↔ Commute x (y₀ : G.C) := by
    intro x
    rw [hEc, Subalgebra.mem_centralizer_iff]
    constructor
    · intro h; exact (h (y₀ : G.C) (Set.mem_singleton _)).symm
    · intro h g hg; rw [Set.mem_singleton_iff.1 hg]; exact h.eq.symm
  have hcomm : ∀ a b : Ec, a * b = b * a := fun a b => Subtype.ext
    (GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G y₀ hsep hdeg a b ((memE a).1 a.2) ((memE b).1 b.2)).eq
  letI : CommRing Ec := { (inferInstance : Ring Ec) with mul_comm := hcomm }
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  haveI : FiniteDimensional ℚ Ec := inferInstance
  haveI : IsReduced Ec := ⟨fun x ⟨k, hk⟩ => Subtype.ext (GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly p G y₀ hsep hdeg x ((memE x).1 x.2) k
    (by simpa using congrArg Subtype.val hk))⟩

  have sh_add : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := fun x y => by simp [sh]
  have sh_mul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by simp [sh]
  have sh_one : sh G 1 = 1 := by simp [sh]
  have sh_zero : sh G 0 = 0 := by simp [sh]
  have sh_alg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := fun q => by
    simp only [sh, RingHom.map_rat_algebraMap G.star q, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  have sh_sh : ∀ x, sh G (sh G x) = x := fun x => G.star_star x
  have sh_binv : sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
      rw [← hβ, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : sh G (y₀ : G.C) = 0 := by
      have := congrArg (fun t => ((β⁻¹ : G.Cˣ) : G.C) * (((y₀⁻¹ : G.Cˣ) : G.C) * t)) hy
      simpa [← mul_assoc] using this
    have : (y₀ : G.C) = 0 := by rw [← sh_sh (y₀ : G.C), h0, sh_zero]
    exact y₀.ne_zero this
  have tC_y : (β : G.C) * sh G (y₀ : G.C) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C) := by
    have := congrArg (fun t => ((y₀⁻¹ : G.Cˣ) : G.C) * t * ((β⁻¹ : G.Cˣ) : G.C)) hy
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    rw [this, mul_assoc, Units.mul_inv, mul_one, Algebra.commutes]
  have tC_mul : ∀ x y : G.C, (β : G.C) * sh G (x * y) * ((β⁻¹ : G.Cˣ) : G.C) =
      ((β : G.C) * sh G y * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro x y
    rw [sh_mul]; simp only [mul_assoc, Units.inv_mul_cancel_left]
  have tC_mem : ∀ x : G.C, Commute x (y₀ : G.C) →
      Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (y₀ : G.C) := by
    intro x hx
    have h1 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C)) := by
      rw [← tC_y]
      show _ * _ = _ * _
      rw [← tC_mul, ← tC_mul, hx.eq]
    have h2 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) ((y₀⁻¹ : G.Cˣ) : G.C) := by
      have h3 := h1.smul_right (s⁻¹)
      rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul] at h3
    simpa using h2.units_inv_right

  let τf : Ec → Ec := fun x => ⟨(β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C), (memE _).2 (tC_mem x ((memE x).1 x.2))⟩
  have τf_val : ∀ x : Ec, ((τf x : Ec) : G.C) = (β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := fun x => rfl
  have τf_inv : ∀ x, τf (τf x) = x := by
    intro x; apply Subtype.ext
    rw [τf_val, τf_val, sh_mul, sh_mul, sh_sh, hβ, sh_binv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [Units.mul_inv, mul_one]
  let τa : Ec →ₐ[ℚ] Ec :=
    { toFun := τf
      map_one' := by apply Subtype.ext; rw [τf_val]; simp [sh_one]
      map_mul' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_mul, tC_mul, ← τf_val, ← τf_val, ← Subalgebra.coe_mul, hcomm]
      map_zero' := by apply Subtype.ext; rw [τf_val]; simp [sh_zero]
      map_add' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_add, sh_add, mul_add, add_mul]; rfl
      commutes' := by
        intro q; apply Subtype.ext
        rw [τf_val]
        change (β : G.C) * sh G (algebraMap ℚ G.C q) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C q
        rw [sh_alg, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  have τa_apply : ∀ x, τa x = τf x := fun x => rfl
  let τe : Ec ≃ₐ[ℚ] Ec := AlgEquiv.ofAlgHom τa τa (AlgHom.ext fun x => τf_inv x) (AlgHom.ext fun x => τf_inv x)
  have τe_apply : ∀ x, τe x = τf x := fun x => rfl
  have τe_inv : ∀ x, τe (τe x) = x := fun x => τf_inv x

  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one G.F)
  set jF : G.F := x₁ - IsCMField.complexConj G.F x₁ with hjF
  have hjF0 : jF ≠ 0 := by
    rw [hjF, sub_ne_zero]; intro h; exact hx₁ (by rw [← h]; rfl)
  have hjFc : IsCMField.complexConj G.F jF = -jF := by
    rw [hjF, map_sub, IsCMField.complexConj_apply_apply]; ring
  have cen : ∀ z : G.F, algebraMap G.F G.C z ∈ Ec := fun z => (memE _).2 (Algebra.commutes z (y₀ : G.C))
  let jE : Ec := ⟨algebraMap G.F G.C jF, cen jF⟩
  have hjE : IsUnit jE := by
    have h : jE * ⟨algebraMap G.F G.C jF⁻¹, cen _⟩ = 1 := by
      apply Subtype.ext
      change algebraMap G.F G.C jF * algebraMap G.F G.C jF⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hjF0, map_one]
    exact ⟨⟨jE, _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have hjτ : τe jE = -jE := by
    apply Subtype.ext
    rw [τe_apply, τf_val]
    change (β : G.C) * (G.star (algebraMap G.F G.C jF)).unop * ((β⁻¹ : G.Cˣ) : G.C) = -algebraMap G.F G.C jF
    rw [G.star_F, hjFc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one, map_neg]
  obtain ⟨A', hA'⟩ := GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms Ec τe τe_inv jE hjE hjτ S
  refine ⟨A'.image Subtype.val, ?_⟩
  intro a ha hac hafix hloc

  obtain ⟨ua, rfl⟩ := ha
  have ha' : (ua : G.C) ∈ Ec := (memE _).2 hac
  set a' : Ec := ⟨ua, ha'⟩ with ha'def
  have hinvE : ((ua⁻¹ : G.Cˣ) : G.C) ∈ Ec := (memE _).2 hac.units_inv_left
  have ha'u : IsUnit a' := by
    have h : a' * ⟨_, hinvE⟩ = 1 := Subtype.ext ua.mul_inv
    exact ⟨⟨a', _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have ha'fix : τe a' = a' := Subtype.ext hafix
  have hloc' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : Ec), c ≠ 0 ∧ IsUnit b ∧
      a' = x * (algebraMap ℚ Ec c * (b * τe b)) ∧
      algebraMap ℚ Ec c * (b * τe b) = y * a' ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : Ec) * x) ∧
        IsIntegral ℤ ((d : Ec) * y) := by
    intro ℓ hℓ hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨u, z, hzc, hz⟩ := hloc ℓ hℓS
    obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.tensor_centralizer_injective_commutant_eq ℚ_[ℓ] G.C (y₀ : G.C)
    set ι := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) Ec.val with hι
    have hinCy : inC G ℚ_[ℓ] (y₀ : G.C) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (y₀ : G.C) := rfl
    obtain ⟨w, hw⟩ := hsurj z (hinCy ▸ hzc)
    obtain ⟨w2, hw2⟩ := hsurj ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ) : ℚ_[ℓ] ⊗[ℚ] G.C) (hinCy ▸ hzc.units_inv_left)
    have hww : w * w2 = 1 := hinj (by rw [map_mul, hw, hw2, Units.mul_inv, map_one])
    let Z : (ℚ_[ℓ] ⊗[ℚ] Ec)ˣ := ⟨w, w2, hww, by rw [mul_comm]; exact hww⟩
    set τℓ := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τe.toAlgHom with hτℓ
    have hkey : ∀ t : ℚ_[ℓ] ⊗[ℚ] Ec, ι (τℓ t) = inC G ℚ_[ℓ] (β : G.C) * (starT G.star ℚ_[ℓ] (ι t)).unop *
        inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        rw [hτℓ, hι, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          starT_tmul]
        simp only [inC, AlgHom.id_apply, Subalgebra.coe_val, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rfl
      | add t1 t2 h1 h2 => rw [map_add, map_add, h1, h2, map_add, map_add, MulOpposite.unop_add, mul_add, add_mul]
    have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a' = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] Ec) (u : ℚ_[ℓ]) *
        ((Z : ℚ_[ℓ] ⊗[ℚ] Ec) * τℓ (Z : ℚ_[ℓ] ⊗[ℚ] Ec)) := by
      apply hinj
      rw [map_mul, map_mul, AlgHom.commutes, hkey]
      have hZ : ι (Z : ℚ_[ℓ] ⊗[ℚ] Ec) = z := hw
      rw [hZ, hι, Algebra.TensorProduct.map_tmul]
      change inC G ℚ_[ℓ] (ua : G.C) = _
      rw [hz]
      simp only [mul_assoc]
    obtain ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩ := GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm Ec τe.toAlgHom ℓ a' u Z ha'u heq
    exact ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩
  obtain ⟨a₀, ha₀, r, e, hre⟩ := hA' a' ha'u ha'fix hloc'
  refine ⟨(a₀ : G.C), Finset.mem_image_of_mem _ ha₀, r, Units.map (Ec.val : Ec →* G.C) e, (memE _).1 (e : Ec).2, ?_⟩
  rw [τe_apply] at hre
  have := congrArg Subtype.val hre
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, τf_val] at this
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftCosetRepresentativesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_left_coset_representatives : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r), ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  first | (exact @GlobalTheory.orbFin_KHT_cmd) | (exact GlobalTheory.orbFin_KHT_cmd) | (intros; apply GlobalTheory.orbFin_KHT_cmd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongruStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  first | exact @GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | exact GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | (intros; apply GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorSquaredBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_squared_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKCx.entries_sq_le_of_fixL) | (exact GlobalTheory.LKCx.entries_sq_le_of_fixL) | (intros; apply GlobalTheory.LKCx.entries_sq_le_of_fixL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrixStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.flag_conv | exact GlobalTheory.FlagPush.flag_conv | (intros; apply GlobalTheory.FlagPush.flag_conv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

noncomputable def permRowsGL {K : Type} [CommRing K] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) K) :
    GL (Fin N) K :=
  GeneralLinearGroup.mk'' (g.1.submatrix w id) (by
    rw [det_permute]
    exact ((Equiv.Perm.sign w).isUnit.map (Int.castRingHom _)).mul ((isUnit_iff_isUnit_det _).1 g.isUnit))

theorem exists_flagPt_eq_comp_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) {K : Type} [Field K] (g : ι → GL (Fin N) K) :
    ∃ (w : ι → Equiv.Perm (Fin N)) (ψ : CellRing a l →+* K), flagPt a l g = spMap ψ ≫ cell a l w := by
  choose w hw using fun τ => GlobalTheory.GL_exists_perm_rows_leading_minors_ne_zero K N (g τ)
  choose L b hLb hL hb using fun τ => GlobalTheory.T.block_lu_decomposition_exists K N {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}
    (permRowsGL (w τ) (g τ)) fun k hk => (hw τ k hk).isUnit
  have hB (τ : ι) (i j : Fin N) : Below a l τ i j ↔
      ∃ s ∈ {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}, (j : ℕ) < s ∧ s ≤ (i : ℕ) :=
    ⟨fun ⟨k, h₁, h₂⟩ => ⟨_, ⟨k, h₁, rfl⟩, h₂⟩, fun ⟨_, ⟨k, h₁, e⟩, h₂⟩ => ⟨k, h₁, e ▸ h₂⟩⟩
  have e : g = (fun τ => permRowsGL (w τ).symm (L τ)) * b := by
    funext τ
    ext i j
    have := congrArg (fun m : GL (Fin N) K => m.1 ((w τ).symm i) j) (hLb τ)
    simpa [permRowsGL, Matrix.mul_apply] using this
  refine ⟨fun τ => (w τ).symm, _, e.symm ▸ flagPt_eq_comp_cell a l (fun τ => (w τ).symm)
    (fun τ => permRowsGL (w τ).symm (L τ)) b (fun τ i j h => ?_) fun τ i j h => hb τ i j ((hB _ _ _).1 h)⟩
  exact hL τ _ j fun h' => h ((hB _ _ _).2 h')

theorem exists_mem_range_cell (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (x : Part a l) : ∃ w : ι → Equiv.Perm (Fin N), x ∈ Set.range (cell a l w) := by
  obtain ⟨p, rfl⟩ := GlobalTheory.T.flag_orbit_map_surjective ι κ N a l x
  let q : PrimeSpectrum (GLRing ι N) := p
  let ψ : GLRing ι N →+* q.asIdeal.ResidueField := algebraMap _ _
  obtain ⟨w, φ, h⟩ := exists_flagPt_eq_comp_cell a l fun τ => GeneralLinearGroup.map ψ (univGL ι N τ)
  rw [flagPt, evalGL_map_univGL] at h
  let o : Sp q.asIdeal.ResidueField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have hp : spMap ψ o = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap ψ ⊥ = q.asIdeal
    exact Ideal.ker_algebraMap_residueField _
  refine ⟨w, spMap φ o, ?_⟩
  rw [← hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignaturesStatement
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAction_quadraticOperators_factorSignatures : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  first | exact @GlobalTheory.HoweD.quad_fockD | exact GlobalTheory.HoweD.quad_fockD | (intros; apply GlobalTheory.HoweD.quad_fockD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  first | exact @GlobalTheory.FockPos.fock_monomial_zero_of_on | exact GlobalTheory.FockPos.fock_monomial_zero_of_on | (intros; apply GlobalTheory.FockPos.fock_monomial_zero_of_on <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealIntegralLattice
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_integral_lattice : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (exact GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnitStatement
section
open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.prime_not_isUnit | exact GlobalTheory.ExpFrame.Frame.prime_not_isUnit | (intros; apply GlobalTheory.ExpFrame.Frame.prime_not_isUnit <;> assumption)
end

