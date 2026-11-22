import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalIsomorphismTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_rep_pow_of_le : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  intro p _ D R _ b N w0 r r' hrr' S _ s o H i hHf hHe hi hH
  haveI := hHf
  haveI := hHe
  have hmh := o.act.hom

  let kil : ∀ (T : Over S) (x : T ⟶ o.A), Ideal (𝓞 D.F) := fun T x =>
    { carrier := {c | x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1}
      add_mem' := by
        intro a c ha hc
        simp only [Set.mem_ofPred_eq] at ha hc ⊢
        rw [map_add, o.act.add, comp_mul, ha, hc, _root_.mul_one]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        have h0 := o.act.add 0 0
        rw [add_zero] at h0
        have h1 : x ≫ o.act.act 0 = x ≫ o.act.act 0 * x ≫ o.act.act 0 := by rw [← comp_mul, ← h0]
        exact mul_eq_left.1 h1.symm
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hc ⊢
        rw [map_mul, o.act.mul, ← Category.assoc, hc, one_comp] }
  obtain ⟨s0, hs0⟩ := IsNoetherian.noetherian (w0 ^ r)
  have hgen : ∀ (T : Over S) (x : T ⟶ o.A),
      (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ↔
        ∀ c : s0, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    constructor
    · intro h c
      exact h c (hs0 ▸ Submodule.subset_span c.2)
    · intro h c hc
      have hle : Submodule.span (𝓞 D.F) (s0 : Set (𝓞 D.F)) ≤ kil T x :=
        Submodule.span_le.2 fun c hc => h ⟨c, hc⟩
      rw [← hs0] at hc
      exact hle hc
  have hle : w0 ^ r' ≤ w0 ^ r := Ideal.pow_le_pow_right hrr'
  have hmono : ∀ (T : Over S) (y y' : T ⟶ H), y ≫ i = y' ≫ i → y = y' := by
    intro T y y' e
    have hk : ∀ c ∈ w0 ^ r', (y' ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
      rw [Category.assoc, hi c hc, comp_one]
    exact (hH T _ hk).unique e rfl
  have hf0 : ∀ c : s0, ∃ f : H ⟶ H, f ≫ i = i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := by
    intro c
    refine (hH H _ fun c' hc' => ?_).exists
    rw [Category.assoc, ← o.act.mul, ← map_mul]
    exact hi _ (Ideal.mul_mem_right _ _ hc')
  choose f hf using hf0
  obtain ⟨e, he⟩ := (hH _ (1 : 𝟙_ (Over S) ⟶ o.A) fun c _ => one_comp _).exists
  have htr : ∀ (T : Over S) (h : T ⟶ H), (∀ c : s0, h ≫ f c = h ≫ toUnit H ≫ e) ↔
      ∀ c ∈ w0 ^ r, (h ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T h
    rw [hgen]
    refine forall_congr' fun c => ⟨fun e1 => ?_, fun e1 => ?_⟩
    · have e2 := congrArg (· ≫ i) e1
      simp only [Category.assoc, hf, he, comp_one] at e2
      rw [Category.assoc]
      exact e2
    · apply hmono
      simp only [Category.assoc, hf, he, comp_one]
      rw [← Category.assoc]
      exact e1
  obtain ⟨U, hUc, hU⟩ := GlobalTheory.LevCover.ClopenCond.forall_finite (T := H)
    (P := fun (c : s0) (T' : Over S) (h : T' ⟶ H) => h ≫ f c = h ≫ toUnit H ≫ e)
    fun c => GlobalTheory.LevCover.clopenCond_eq (f c) (toUnit H ≫ e)
  obtain ⟨K, iK, hKf, hKe, hiKm, hiK⟩ := GlobalTheory.LevCover.exists_sub U hUc
  refine ⟨K, iK ≫ i, hKf, hKe, ?_, ?_⟩
  · exact (htr K iK).1 ((hU K iK).2 ((hiK K iK).2 ⟨𝟙 _, Category.id_comp _⟩))
  · intro T x hx
    have hx' : ∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hx c (hle hc)
    obtain ⟨y0, hy0, -⟩ := hH T x hx'
    have hr : Set.range y0.left ⊆ U := (hU T y0).1 ((htr T y0).2 (by rw [hy0]; exact hx))
    obtain ⟨y, hy⟩ := (hiK T y0).1 hr
    refine ⟨y, show y ≫ iK ≫ i = x by rw [← Category.assoc, hy, hy0], fun y' hy' => ?_⟩
    haveI := hiKm
    apply (cancel_mono iK).1
    apply hmono
    rw [Category.assoc, Category.assoc, hy', ← Category.assoc, hy, hy0]

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanKill

theorem exists_mem_pow_forall_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] (β : R →+* k), ∃ c ∈ w0 ^ r, ∀ i, β (b.t i c) ≠ 0 := by
  intro p _ D R _ b w0 r hw k _ β
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos D.a with ha | ha
  · obtain ⟨i, -⟩ := hcon 0 (zero_mem _)
    exact (Fin.elim0 (ha ▸ i))
  let i0 : Fin D.a := ⟨0, ha⟩
  have hsub : ((w0 ^ r : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) ⊆
      ⋃ i ∈ ((Finset.univ : Finset (Fin D.a)) : Set (Fin D.a)), (RingHom.ker (β.comp (b.t i)) : Set (𝓞 D.F)) := by
    intro c hc
    obtain ⟨i, hi⟩ := hcon c hc
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) (RingHom.mem_ker.mpr hi)
  obtain ⟨i, -, hi⟩ := (Ideal.subset_union_prime i0 i0 (fun i _ _ _ => RingHom.ker_isPrime _)).mp hsub
  have hi' : w0 ≤ RingHom.ker (β.comp (b.t i)) := (RingHom.ker_isPrime _).le_of_pow_le hi
  have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hi' hy))
  rw [hw.2.2.1 i, top_le_iff] at hle
  exact RingHom.ker_ne_top β hle

theorem exists_mem_pow_add_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (β : R →+* k) (r2 : ℤ), (r2 : k) = (D.tr : k) - β b.ρ → ∃ c ∈ w0 ^ r, ∃ e f : 𝓞 D.F, c + e * (D.ω - (r2 : 𝓞 D.F)) + f * (p : 𝓞 D.F) = 1 := by
  intro p _ D R _ b w0 r hw k _ _ _ β r2 hr2
  haveI : w0.IsMaximal := hw.1
  letI : Field (𝓞 D.F ⧸ w0) := Ideal.Quotient.field w0

  have hpQ : ((p : 𝓞 D.F ⧸ w0)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w0), Ideal.Quotient.eq_zero_iff_mem]; exact hw.2.1
  haveI : CharP (𝓞 D.F ⧸ w0) p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hpQ
  have hne : w0 ≠ ⊥ := by
    intro h
    have h1 := hw.2.1
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1
  haveI : Finite (𝓞 D.F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  letI : Algebra (ZMod p) (𝓞 D.F ⧸ w0) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 D.F ⧸ w0) := inferInstance
  let φ0 := IsAlgClosed.lift (M := k) (R := ZMod p) (S := 𝓞 D.F ⧸ w0)
  let φ : 𝓞 D.F →+* k := φ0.toRingHom.comp (Ideal.Quotient.mk w0)
  have hker : RingHom.ker φ = w0 := by
    ext y
    rw [RingHom.mem_ker]
    change φ0 (Ideal.Quotient.mk w0 y) = 0 ↔ y ∈ w0
    rw [map_eq_zero_iff φ0 φ0.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hφ := hw.2.2.2 k β φ hker

  let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), (p : 𝓞 D.F)}
  have hJ : w0 ⊔ J = ⊤ := by
    by_contra hsup
    have hle : J ≤ w0 := by
      have := hw.1.eq_of_le hsup le_sup_left
      exact this ▸ le_sup_right
    have hmem : D.ω - (r2 : 𝓞 D.F) ∈ w0 := hle (Ideal.subset_span (Set.mem_insert _ _))
    rw [← hker, RingHom.mem_ker, map_sub, map_intCast, hφ, hr2] at hmem
    have hρ : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
      have h := congrArg β b.ρ_root
      simpa using h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-((D.tr : k) - 2 * β b.ρ)) * hmem - 4 * hρ
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hJr : w0 ^ r ⊔ J = ⊤ := by
    have h := Ideal.isCoprime_iff_sup_eq.mpr hJ
    exact Ideal.isCoprime_iff_sup_eq.mp h.pow_left
  obtain ⟨c, hc, j, hj, hcj⟩ := Submodule.mem_sup.mp (hJr ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ w0 ^ r ⊔ J)
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
  exact ⟨c, hc, e, f, by rw [add_assoc, hef, hcj]⟩

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem sum_eq_zero_of_eigen (T : Module.End k V) {I : Type} [DecidableEq I] (s : Finset I) :
    ∀ (w : I → V) (l : I → k), (∀ i ∈ s, T (w i) = l i • w i) → (∀ i ∈ s, l i ≠ 0) →
      T (∑ i ∈ s, w i) = 0 → ∑ i ∈ s, w i = 0 := by
  induction s using Finset.induction_on with
  | empty => intros; simp
  | insert j s hj ih =>
    intro w l hw hl hT
    rw [Finset.sum_insert hj] at hT ⊢
    have e : ∑ i ∈ s, (l i - l j) • w i = T (w j + ∑ i ∈ s, w i) - l j • (w j + ∑ i ∈ s, w i) := by
      rw [map_add, map_sum, hw j (Finset.mem_insert_self j s), smul_add, Finset.smul_sum,
        Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_insert_of_mem hi))]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have key := ih (fun i => (l i - l j) • w i) l
      (fun i hi => by rw [map_smul, hw i (Finset.mem_insert_of_mem hi), smul_comm])
      (fun i hi => hl i (Finset.mem_insert_of_mem hi))
      (by rw [e, map_sub, map_smul, hT, map_zero, smul_zero, sub_zero])
    rw [key, hT, zero_sub, eq_comm, neg_eq_zero] at e
    exact (smul_eq_zero.mp e).resolve_left (hl j (Finset.mem_insert_self j s))

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

lemma L_int {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℤ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

lemma L_nat {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℕ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_natCast, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

theorem core {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (v : V) (hv : ∀ c ∈ w0 ^ r, L c v = 0) : v = 0 := by
  by_cases hp : (p : k) = 0
  swap
  · have h := hv _ (Ideal.pow_mem_pow hw.2.1 r)
    rw [← Nat.cast_pow, L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left (by rw [Nat.cast_pow]; exact pow_ne_zero _ hp)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hp
  set Tω := L D.ω with hTω
  set ρ1 := β b.ρ with hρ1
  set ρ2 := (D.tr : k) - ρ1 with hρ2
  have hquad : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    have hb : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
    have h := D.nm_eq
    rw [hb] at h
    linear_combination (-1 : 𝓞 D.F) * h
  have hq : ∀ u, Tω (Tω u) = (D.tr : k) • Tω u - (D.nm : k) • u := by
    intro u
    have h := congrArg (fun f => f u) (congrArg L hquad)
    simp only [map_add, map_sub, map_mul, map_zero, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, L_int] at h
    rw [← hTω] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hρ : ρ1 ^ 2 - (D.tr : k) * ρ1 + (D.nm : k) = 0 := by
    have h := congrArg β b.ρ_root
    simpa using h
  have hsum : ρ1 + ρ2 = D.tr := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = D.nm := by rw [hρ2]; linear_combination (-1 : k) * hρ
  clear_value Tω ρ1 ρ2
  have hδ : ρ1 - ρ2 ≠ 0 := by
    intro h0
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      have : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = (ρ1 - ρ2) ^ 2 := by
        push_cast
        rw [← hsum, ← hprod]; ring
      rw [this, h0]; ring
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hcomm : ∀ c u, L c (Tω u) = Tω (L c u) := by
    intro c u
    rw [hTω, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  set v1 := (ρ1 - ρ2)⁻¹ • (Tω v - ρ2 • v) with hv1
  set v2 := (ρ1 - ρ2)⁻¹ • (ρ1 • v - Tω v) with hv2
  have hv12 : v = v1 + v2 := by
    rw [hv1, hv2, ← smul_add]
    have : Tω v - ρ2 • v + (ρ1 • v - Tω v) = (ρ1 - ρ2) • v := by rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have e1 : Tω v1 = ρ1 • v1 := by
    rw [hv1, map_smul, map_sub, map_smul, hq, smul_comm ρ1]
    congr 1
    rw [← hsum, ← hprod]
    module
  have e2 : Tω v2 = ρ2 • v2 := by
    rw [hv2, map_smul, map_sub, map_smul, hq, smul_comm ρ2]
    congr 1
    rw [← hsum, ← hprod]
    module
  have k1 : ∀ c ∈ w0 ^ r, L c v1 = 0 := by
    intro c hc
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : ∀ c ∈ w0 ^ r, L c v2 = 0 := by
    intro c hc
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have z1 : v1 = 0 := by
    obtain ⟨c, hc, hne⟩ := exists_mem_pow_forall_ne_zero p D R b w0 r hw k β
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1 c hc
  have z2 : v2 = 0 := by
    obtain ⟨r0, hr0⟩ := D.split
    have hr0k : ((r0 : k) - ρ1) * ((r0 : k) - ρ2) = 0 := by
      have : ((r0 ^ 2 - D.tr * r0 + D.nm : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hr0
      push_cast at this
      linear_combination this - (r0 : k) * hsum + hprod
    obtain ⟨r2, hr2⟩ : ∃ r2 : ℤ, (r2 : k) = ρ2 := by
      rcases mul_eq_zero.mp hr0k with h | h
      · exact ⟨D.tr - r0, by push_cast; rw [hρ2]; linear_combination -h⟩
      · exact ⟨r0, by linear_combination h⟩
    obtain ⟨c, hc, e, f, hcef⟩ := exists_mem_pow_add_eq_one p D R b w0 r hw k β r2 (by rw [hr2, hρ2, hρ1])
    have h := congrArg (fun g => g v2) (congrArg L hcef)
    simp only [map_add, map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2 c hc] at h
    simp only [zero_add, add_zero] at h
    rw [← hTω, e2, hr2, map_smul, sub_self, hp, zero_smul, map_zero, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_etPlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  intro p _ D R _ b N w0 r hw S s o k _ _ x v hv0 hv
  set β : R →+* k := (Spec.preimage (x ≫ s)).hom with hβ
  have hx : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hlie : ∀ u : Tan x o.A, L D.ω u = β b.ρ • u →
      ∃ w : Fin D.a → Tan x o.A, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ u = ∑ i, w i := by
    intro u hu
    obtain ⟨w, hw1, hw2⟩ := o.lie k β x hx u.hom
      ⟨(mem_tanSub_iff x o.A _).mp u.hom_mem, by
        have := congrArg (fun t : Tan x o.A => t.hom.left) hu
        simpa [hL, GrpTangentPt.epsScalePt_left] using this⟩
    have hmem : ∀ i, w i ∈ tanSub x o.A := fun i => (mem_tanSub_iff x o.A _).mpr (hw1 i 0).1
    refine ⟨fun i => Tan.mk (w i) (hmem i), fun i c => Tan.ext (Over.OverMorphism.ext ((hw1 i c).2)), ?_⟩
    refine Tan.ext ?_
    rw [Tan.hom_sum, hw2, List.prod_ofFn]
    rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have := core D b w0 r hw β L hlie (Tan.mk v hmv) (fun c hc => Tan.ext (by rw [hL]; exact hv c hc))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem four_f_r_le_k_pow_eight (R : Ranks) : 4 * R.f * R.r ≤ R.k ^ 8 := by
  have hf : R.f ≤ R.k := by
    unfold Ranks.f Ranks.n
    exact R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hr : R.r ≤ 2 * R.k := by
    unfold Ranks.r
    omega
  have hk : 2 ≤ R.k := by omega
  have h6 : 8 ≤ R.k ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)
  calc 4 * R.f * R.r ≤ 4 * R.k * (2 * R.k) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = 8 * R.k ^ 2 := by ring
    _ ≤ R.k ^ 6 * R.k ^ 2 := Nat.mul_le_mul_right _ h6
    _ = R.k ^ 8 := by ring

theorem four_f_r_le_min_g_of_sizeG {D : D7} (L : SizeData₂ D) (h : SizeG L) : Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D := by
  have hb : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _)
  have key : ∀ i : Fin 2, 4 * D.R.f * D.R.r ≤ D.host.g i := by
    intro i
    have h1 := (h i i).1
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
      pow_le_pow_left₀ hk (le_mul_of_one_le_right hk hb) 8
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
    exact (four_f_r_le_k_pow_eight D.R).trans h3
  unfold Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound
  exact le_min (key 0) (key 1)

theorem four_f_r_le_min_g_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x →
    ∀ i : Fm.Ix x, Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound (Fm.D x i) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := Fm.sizes x hx i
  exact four_f_r_le_min_g_of_sizeG _ hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreMulKTorsorHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fibre_mulK_torsor_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (exact GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK) | (intros; apply GlobalTheory.UPel.HT.Hecke.FibreMulK.fibre_mulK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpPullback_prod_self_isPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  first | exact @GlobalTheory.AbCoh.prod_pullback_sq | exact GlobalTheory.AbCoh.prod_pullback_sq | (intros; apply GlobalTheory.AbCoh.prod_pullback_sq <;> assumption)
end

