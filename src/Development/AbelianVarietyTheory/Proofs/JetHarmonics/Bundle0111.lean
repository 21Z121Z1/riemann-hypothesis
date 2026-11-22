import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0109
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Transfer
variable {q : ℕ} [Fact q.Prime]

def Tr (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (p : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ (fun z => F (z + p)) 0 ∧ Bdd (hat ι ℓ F) ∧
    hat ι ℓ (fun z => F (z + p)) = shiftS ζ (hat ι ℓ F)

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).1⟩

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).2⟩

section
variable {ι : ℂ ≃+* ℂ_[q]} {ℓ : ℂ_[q]⟦X⟧} {ζ : ℂ_[q]} {p : ℂ}

lemma Tr.const (h0 : constantCoeff ℓ = 0) (c : ℂ) : Tr ι ℓ ζ p (fun _ => c) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).2.1 c
  refine ⟨analyticAt_const, analyticAt_const, ⟨‖ι c‖, fun n => ?_⟩, ?_⟩
  · rw [h, coeff_C]
    split_ifs <;> simp
  · rw [h, Shift.shiftS_C]

lemma Tr.add (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z + G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.add g1, f2.add g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).1]; exact bdd_add f3 g3
  · rw [(h _ _ f1 g1).1, (h _ _ f2 g2).1, f4, g4, Shift.shiftS_add hζ f3 g3]

lemma Tr.mul (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z * G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.mul g1, f2.mul g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).2.1]; exact bdd_mul f3 g3
  · rw [(h _ _ f1 g1).2.1, (h _ _ f2 g2).2.1, f4, g4, Shift.shiftS_mul hζ f3 g3]

lemma Tr.pow (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F : ℂ → ℂ} (hF : Tr ι ℓ ζ p F) (n : ℕ) :
    Tr ι ℓ ζ p (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 1
  | succ n ih => simpa only [pow_succ] using Tr.mul h0 hζ ih hF

lemma Tr.sum (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) (F : ℕ → ℂ → ℂ) (hF : ∀ i, Tr ι ℓ ζ p (F i))
    (n : ℕ) : Tr ι ℓ ζ p (fun z => ∑ i ∈ Finset.range n, F i z) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 0
  | succ n ih => simpa only [Finset.sum_range_succ] using Tr.add h0 hζ ih (hF n)

lemma exists_homog (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {u w : ℂ → ℂ} (hu : Tr ι ℓ ζ p u)
    (hw : Tr ι ℓ ζ p w) (A : Polynomial ℂ) :
    ∃ (k : ℕ) (F : ℂ → ℂ), Tr ι ℓ ζ p F ∧ ∀ z x : ℂ, x * w z = u z → F z = A.eval x * w z ^ k := by
  refine ⟨A.natDegree, fun z => ∑ i ∈ Finset.range (A.natDegree + 1),
    A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)), ?_, fun z x hx => ?_⟩
  · exact Tr.sum h0 hζ (fun i z => A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)))
      (fun i => Tr.mul h0 hζ (Tr.const h0 _) (Tr.mul h0 hζ (hu.pow h0 hζ i) (hw.pow h0 hζ _))) _
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi'
    rw [← hx, hj, Nat.add_sub_cancel_left]
    ring

lemma exists_quot (h0 : constantCoeff ℓ = 0) (h1 : coeff 1 ℓ ≠ 0) {f D N : ℂ → ℂ} (S : ℂ_[q]⟦X⟧)
    (hf : MeromorphicAt f 0) (hD : AnalyticAt ℂ D 0) (hN : AnalyticAt ℂ N 0)
    (hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0) (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z * D z = N z)
    (hS : S * hat ι ℓ D = hat ι ℓ N) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
  obtain ⟨h, hc, hid, hcc, -⟩ := TaylorRead.hat_laws q ι ℓ h0
  have hDne : hat ι ℓ D ≠ 0 := by
    intro hz
    have e : hat ι ℓ D = hat ι ℓ (fun _ => 0) := by rw [hz, hc]; simp
    have e2 := (h _ _ hD analyticAt_const).2.2.2 h1 e
    obtain ⟨z, hz1, hz2⟩ := (hD0.and (e2.filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  have hpow : ∀ n : ℕ, hat ι ℓ (fun z => z ^ n) = ℓ ^ n := by
    intro n
    induction n with
    | zero => simpa using hc 1
    | succ n ih =>
      simp only [pow_succ]
      rw [(h (fun z => z ^ n) (fun z => z) (by fun_prop) (by fun_prop)).2.1, ih, hid]
  have key : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      hat ι ℓ g = ℓ ^ n * S := by
    intro n g hg hge
    apply mul_right_cancel₀ hDne
    rw [mul_assoc, hS, ← hpow, ← (h _ _ hg hD).2.1, ← (h (fun z => z ^ n) N (by fun_prop) hN).2.1]
    refine (h _ _ (hg.mul hD) (AnalyticAt.mul (by fun_prop) hN)).2.2.1 ?_
    filter_upwards [hge, he] with z a b
    show g z * D z = z ^ n * N z
    rw [a, ← b, mul_assoc]
  have main : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
    intro n
    induction n with
    | zero =>
      intro g hg hge
      exact ⟨g, hg, by simpa using hge, by simpa using key 0 g hg hge⟩
    | succ n ih =>
      intro g hg hge
      have hg0 : g 0 = 0 := by
        have := congrArg constantCoeff (key _ g hg hge)
        rw [hcc] at this
        simpa [h0] using this
      obtain ⟨s, hs⟩ := hg
      refine ih (dslope g 0) ⟨_, hs.has_fpower_series_dslope_fslope⟩ ?_
      filter_upwards [hge, self_mem_nhdsWithin] with z a hz
      have hz' : z ≠ 0 := hz
      rw [dslope_of_ne _ hz', slope_def_field, hg0, a]
      field_simp
      ring
  obtain ⟨n, hn⟩ := hf
  exact main n _ hn (Filter.Eventually.of_forall fun z => by simp)
end

lemma x_ne (M : Mdl q) (hM : M.Ok) (c z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, M.x z - c ≠ 0 := by
  obtain ⟨-, -, hx, -, u0, w0, du, -, hs⟩ := uw_elliptic_flow q M hM
  have hm : Meromorphic (fun z => M.x z - c) := fun z => (hx.1 z).sub (MeromorphicAt.const c z)
  have h0 : meromorphicOrderAt (fun z => M.x z - c) 0 ≠ ⊤ := by
    intro ht
    rw [meromorphicOrderAt_eq_top_iff] at ht
    obtain ⟨au, aw, -, -, e1, e2⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
    have dw : deriv M.w 0 = 0 := by
      have := e2.self_of_nhds.2.2
      simpa [u0, w0] using this
    have e3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u z = c * M.w z := by
      filter_upwards [ht, e1] with z a b
      rw [← b.2.2.1, sub_eq_zero.mp a]
    have e4 : M.u =ᶠ[𝓝 0] fun z => c * M.w z := by
      rw [eventually_nhdsWithin_iff] at e3
      filter_upwards [e3] with z a
      by_cases hz : z = 0
      · simp [hz, u0, w0]
      · exact a hz
    have := e4.deriv_eq
    rw [du, deriv_const_mul _ aw.differentiableAt, dw, mul_zero] at this
    exact hM.1 this
  have h1 := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩ z₀
  rcases (hm z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h) h1
  · exact h

lemma tendsto_add_punct (p : ℂ) : Filter.Tendsto (fun z : ℂ => z + p) (𝓝[≠] 0) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 (0 + p)) :=
      (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem shift_eq_hat_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  intro q _ M ω ζ p φ hch hat' hφ hφ0 hφb
  have hM : M.Ok := hch.1
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hζ : ‖ζ - 1‖ < 1 := hat'.2.1
  obtain ⟨h1, v, xs, ys, -, -, bys, -, -, cys, -, hwy, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hch
  obtain ⟨tu, tw⟩ := GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hch hat'
  obtain ⟨m, P, A, B, -, hAB⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hM hφ
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := uw_elliptic_flow q M hM
  obtain ⟨au0, aw0, -, -, e0, -⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨aup, awp, -, -, ep, -⟩ := hs p hat'.1
  have htr : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu : Tr M.ι (C ω * logS) ζ p M.u :=
    ⟨au0, aup.comp_of_eq htr (zero_add p), ⟨1, hch.2.2.1⟩, tu⟩
  have hw : Tr M.ι (C ω * logS) ζ p M.w := by
    refine ⟨aw0, awp.comp_of_eq htr (zero_add p), ⟨1, ?_⟩, tw⟩
    refine (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 bys cys ?_
    rw [pow_zero, one_mul, mul_comm, hwy]
    intro n
    rw [map_neg, norm_neg, coeff_X_pow]
    split_ifs <;> simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hQ
  obtain ⟨a, FQ, tQ, eQ⟩ := exists_homog h0 hζ hu hw Q
  obtain ⟨b, FA, tA, eA⟩ := exists_homog h0 hζ hu hw A
  obtain ⟨c, FB, tB, eB⟩ := exists_homog h0 hζ hu hw B
  have tD : Tr M.ι (C ω * logS) ζ p (fun z => FQ z * M.w z ^ (b + c + 1)) :=
    tQ.mul h0 hζ (hw.pow h0 hζ _)
  have tN : Tr M.ι (C ω * logS) ζ p
      (fun z => M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b))) :=
    (hw.pow h0 hζ _).mul h0 hζ ((tA.mul h0 hζ (hw.pow h0 hζ _)).add h0 hζ
      ((Tr.const h0 (-1)).mul h0 hζ (tB.mul h0 hζ (hw.pow h0 hζ _))))
  have hid : ∀ z, (z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) →
      φ z * Q.eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z →
      φ z * (FQ z * M.w z ^ (b + c + 1)) =
        M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b)) := by
    intro z e1 e2
    rw [eQ z _ e1.2.2.1, eA z _ e1.2.2.1, eB z _ e1.2.2.1, ← e1.2.2.2]
    linear_combination M.w z ^ (a + b + c + 1) * e2
  have h := (TaylorRead.hat_laws q M.ι _ h0).1
  refine exists_quot h0 h1 _ ?_ tD.2.1 tN.2.1 ?_ ?_ ?_
  · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + p) (hφ.1 _) htr
  · have hQ0 : ∀ᶠ z in 𝓝[≠] p, ∀ i, M.x z - M.x (P i) ≠ 0 :=
      Filter.eventually_all.2 fun i => x_ne M hM _ p
    refine (tendsto_add_punct p).eventually (p := fun z => FQ z * M.w z ^ (b + c + 1) ≠ 0) ?_
    filter_upwards [hQ0, ep] with z a1 a2
    have hw0 : M.w z ≠ 0 := by
      intro hz
      have := a2.2.2.2
      rw [hz] at this
      simp at this
    rw [eQ z _ a2.2.2.1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hw0)) (pow_ne_zero _ hw0)
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using a1 i
  · exact (tendsto_add_punct p).eventually ((ep.and (hAB p)).mono fun z hz => hid z hz.1 hz.2)
  · rw [tD.2.2.2, tN.2.2.2, ← Shift.shiftS_mul hζ hφb tD.2.2.1, ← (h _ _ hφ0 tD.1).2.1]
    congr 1
    exact (h _ _ (hφ0.mul tD.1) tN.1).2.2.1 ((e0.and (hAB 0)).mono fun z hz => hid z hz.1 hz.2)

end GlobalTheory.MomOne.Transfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentOneGenerator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OneGenerator

theorem transport_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {F : Type} [Field F] [Algebra (FractionRing V) F] {n m : ℕ} (h : n = m)
    (θ r₀ r : Fam P.D.toPre F n) (p : QkPt P.D.toPre F n)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε n))) (ζ : F)
    (x : TFK (R := V) F ⟶ P.A.A) (hx : P.ToA F n p x) (hw : w.IsGen) (hf : FinOrd P.D F n p w ζ)
    (hΦ : PhiRel P.D.toPre F n p w θ r₀) (hs : Fam.IsSmul P.D.toPre F ζ r₀ r) :
    ∃ (θ' r₀' r' : Fam P.D.toPre F m) (p' : QkPt P.D.toPre F m)
      (w' : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p'.g.b) (DegPre.lineε m))),
      HEq θ θ' ∧ P.ToA F m p' x ∧ w'.IsGen ∧ FinOrd P.D F m p' w' ζ ∧ PhiRel P.D.toPre F m p' w' θ' r₀' ∧
        Fam.IsSmul P.D.toPre F ζ r₀' r' ∧ HEq r r' := by
  subst h
  exact ⟨θ, r₀, r, p, w, HEq.rfl, hx, hw, hf, hΦ, hs, HEq.rfl⟩

end GlobalTheory.OneGenerator

namespace GlobalTheory

open OneGenerator in

theorem descent_one_generator : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (g g' : ℕ), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' → a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα → ∀ (pb : QkPt P.D.toPre F (1 * g')) (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g')))) (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')), P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 → FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul P.D.toPre F ζb tb₀ tb → ∀ (p : QkPt P.D.toPre F (1 * g' * g)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * g' * g)))) (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (1 * g' * g) p w ζ → P.ToA F (1 * g' * g) p x → x ≫ P.oA.act (star a) = 1 → ∀ (s₂ t₀ r : Fam P.D.toPre F (1 * g' * g)), PullAl P.D F P.oD a (1 * g') g tb s₂ → PhiRel P.D.toPre F (1 * g' * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r → ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g))))) (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))), PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  intro hL _ _ _ V _ _ _ _ E _ _ _ H t P hT
  letI := H.starRing
  intro a a' g g' hg hg' hco haa haa' F _ _ _ θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
    p w ζ x hw hζ hf hx hxa s₂ t₀ r hs₂ hΦ hr
  have hk : 1 ≤ 1 * g' := by omega
  have hkN : 1 ≤ 1 * g' * g := Nat.mul_pos hk hg
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a g (1 * g') hg hk haa
  have key : ∃ (p₂ : QkPt P.D.toPre F (1 * g' * g))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * g' * g))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ : Fam P.D.toPre F (1 * g' * g)),
      P.ToA F (1 * g' * g) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a' * a)) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧
        FinOrd P.D F (1 * g' * g) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * g' * g) p₂ w₂ (π θα) r₀ ∧
        Fam.IsSmul P.D.toPre F ζ₂ r₀ r := by
    by_cases h0 : θα = 0
    · obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V _ P.D F (1 * g') hk pb wb hwb
      have e₀ : tb = 0 := by
        rw [(DVR.isSmul_iff _ _ _).1 hsb, (hΦ' _ _).1 hΦb, h0, map_zero, smul_zero]
      have e₁ : s₂ = π θα := by rw [(hπ _ _).1 hs₂, e₀, h0]
      refine ⟨p, w, ζ, x, t₀, hx, ?_, hw, hζ, hf, e₁ ▸ hΦ, hr⟩
      have := P.oA.hom (star a')
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa, MonObj.one_comp]
    · obtain ⟨p₂, x₂, w₂, ζ₂, t₂, k₁, k₂, k₃, k₄, k₅⟩ := operator_on_pullback_eq_sum hL E H V t P hT a a' g g'
        hg hg' hco haa haa' F θα tb (π θα) s₂ t₀ r h0 ((hπ _ _).2 rfl) hs₂ 1 (fun _ => 1) (fun _ => pb)
        (fun _ => xb) (fun _ => wb) (fun _ => ζb) (fun _ => tb)
        ⟨fun _ => hxb, fun _ => hxba, fun _ => ⟨hwb, hζb, hfb⟩, fun _ => ⟨tb₀, hΦb, hsb⟩, by simp⟩
        p x w ζ hx hxa hw hζ hf hΦ hr
      obtain ⟨r₀, l₁, l₂⟩ := k₄ 0
      have e : r = t₂ 0 := by simpa using k₅
      exact ⟨p₂ 0, w₂ 0, ζ₂ 0, x₂ 0, r₀, k₁ 0, k₂ 0, (k₃ 0).1, (k₃ 0).2.1, (k₃ 0).2.2, l₁, e ▸ l₂⟩
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := key
  obtain ⟨θ', r₀', r', p', w', m₁, m₂, m₃, m₄, m₅, m₆, m₇⟩ :=
    transport_level P (Nat.mul_assoc 1 g' g) (π θα) r₀ r p₂ w₂ ζ₂ x₂ k₁ k₃ k₅ k₆ k₇
  have hc := pullAl_comp hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a a' g g' 1 hg hg' le_rfl haa haa' θ θα (π θα) θ' hθ
    ((hπ _ _).2 rfl) m₁
  rw [_root_.mul_comm a' a] at hc k₂
  exact ⟨θ', p', w', ζ₂, x₂, r₀', r', hc, m₂, k₂, m₃, k₄, m₄, m₅, m₆, m₇⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousCharacter
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.CommutatorCharacter

variable {D : D7} {N N' : ℕ}

theorem Hf_nsmul_swap (T : Tor D) (k : ℕ) (w x : VC D N N') : Hf D T (k • w) x = Hf D T w (k • x) := by
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  ring

theorem kap_add_nsmul (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ) (k : ℕ)
    (u : VC D N N') {w x : VC D N N'} (hw : w ∈ Λ) (hx : k • x ∈ Λ) : kap D T (u + k • w) x = kap D T u x := by
  obtain ⟨a, b, -, h⟩ := hI w hw _ hx
  have him : (Hf D T (k • w) x).im = b := by rw [Hf_nsmul_swap, h]; simp
  unfold kap
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_left, Complex.add_im, him, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

def vecHom (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' :=
  AddMonoidHom.mk' (vecOf D cc δ) (GlobalTheory.PlaceComponents.vecOf_add D cc δ)

theorem vecHom_apply (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    vecHom cc δ A = vecOf D cc δ A := rfl

theorem continuous_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) {X : Type*} [TopologicalSpace X]
    (f : ZMod (p ^ n) → X) : Continuous fun a : ℤ_[p] => f (PadicInt.toZModPow n a) := by
  refine (IsLocallyConstant.comp (f := PadicInt.toZModPow n) ?_ f).continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have hp : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds a hp] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa [dist_eq_norm] using hy

theorem exists_continuous_character :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (Λ : AddSubgroup (VC D N N')), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) Λ →
      ∀ (n r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x : VC D N N'),
      (∀ i, vecOf D cc δ (b i) ∈ Λ) → p ^ n • x ∈ Λ →
      ∃ ψ : C(Fin r → ℤ_[p], ℂ_[p]),
        (∀ a : Fin r → ℤ_[p], ψ a =
          lamC lam (kap D (tor0 D cc δ) (Formalism.L2.Ker.I3.JetMomA.vecZ D (tor0 D cc δ) δ p n b a) x)) ∧
        ∀ a : Fin r → ℤ, ψ (fun i => (a i : ℤ_[p])) =
          lamC lam (kap D (tor0 D cc δ) (vecOf D cc δ (∑ i, (a i : D.host.E) • b i)) x) := by
  intro D cc δ p _ lam N N' Λ hI n r b x hb hx
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let F : (Fin r → ZMod (p ^ n)) → ℂ_[p] := fun c =>
    lamC lam (kap D (tor0 D cc δ) (vecOf D cc δ (∑ i, (((c i).val : ℕ) : D.host.E) • b i)) x)
  have hc : Continuous fun a : Fin r → ℤ_[p] => F fun i => PadicInt.toZModPow n (a i) := by
    letI : TopologicalSpace (ZMod (p ^ n)) := ⊥
    haveI : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
    exact (continuous_of_discreteTopology (f := F)).comp
      (continuous_pi fun i => (continuous_toZModPow n id).comp (continuous_apply i))
  refine ⟨⟨_, hc⟩, fun a => rfl, fun a => ?_⟩
  show F _ = _
  have hw : vecOf D cc δ (∑ i, (a i / (p ^ n : ℕ)) • b i) ∈ Λ := by
    rw [← vecHom_apply, map_sum]
    exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _
  have hs : ∑ i, (a i : D.host.E) • b i =
      ∑ i, (((PadicInt.toZModPow n (a i : ℤ_[p])).val : ℕ) : D.host.E) • b i +
        p ^ n • ∑ i, (a i / (p ^ n : ℕ)) • b i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_intCast, ← Int.cast_natCast, ZMod.val_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul,
      ← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  simp only [F]
  rw [hs, ← vecHom_apply cc δ (_ + _), map_add, map_nsmul, vecHom_apply, vecHom_apply,
    kap_add_nsmul _ hI _ _ hw hx]

end GlobalTheory.CommutatorCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCoprimeMulIntegral
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield GlobalTheory.PlaceComponents

namespace GlobalTheory.IntegralAtBothPrimes

theorem den_coprime_of_norm_le_one {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℂ_[p])‖ ≤ 1) :
    Nat.Coprime q.den p := by
  have h1 : ‖(q : ℚ_[p])‖ ≤ 1 := by
    have := norm_algebraMap' ℂ_[p] (q : ℚ_[p])
    rw [map_ratCast] at this
    rwa [← this]
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  intro hd
  have h2 : ‖((q.den : ℤ) : ℚ_[p])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have h3 : ((q.num : ℤ) : ℚ_[p]) = (q : ℚ_[p]) * ((q.den : ℤ) : ℚ_[p]) := by
    rw [Int.cast_natCast]
    exact_mod_cast (congrArg (fun x : ℚ => (x : ℚ_[p])) (Rat.mul_den_eq_num q)).symm
  have h4 : ‖((q.num : ℤ) : ℚ_[p])‖ < 1 := by
    rw [h3, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h1 (norm_nonneg _) h2
  have h5 : p ∣ q.num.natAbs := Int.natCast_dvd.1 (Padic.norm_intCast_lt_one_iff.1 h4)
  exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced h5 hd)

theorem isIntegral_of_quadratic {K : Type*} [CommRing K] (x : K) (a b : ℤ)
    (h : x ^ 2 - (a : K) * x + (b : K) = 0) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
  exact h

theorem exists_coprime_mul_integral (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : D.host.K)
    (h1 : ‖atP D lam c‖ ≤ 1) (h2 : ‖atPbar D lam c‖ ≤ 1) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ z : 𝓞 D.host.K, (s : D.host.K) * c = (z : D.host.K) := by
  rw [atP₂] at h1
  rw [atPbar_eq, ← homP_conjK] at h2
  obtain ⟨t, n, ht, hn⟩ := exists_trace_norm D c
  have ht1 : ‖(t : ℂ_[p])‖ ≤ 1 := by
    have := congrArg (homP D lam) ht
    rw [map_add, map_ratCast] at this
    rw [← this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hn1 : ‖(n : ℂ_[p])‖ ≤ 1 := by
    have := congrArg (homP D lam) hn
    rw [map_mul, map_ratCast] at this
    rw [← this, norm_mul]
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  refine ⟨t.den * n.den, Nat.Coprime.mul_left (den_coprime_of_norm_le_one t ht1) (den_coprime_of_norm_le_one n hn1), ?_⟩
  have et : (t : D.host.K) * (t.den : D.host.K) = (t.num : D.host.K) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : D.host.K)) (Rat.mul_den_eq_num t)
  have en : (n : D.host.K) * (n.den : D.host.K) = (n.num : D.host.K) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : D.host.K)) (Rat.mul_den_eq_num n)
  have hi : IsIntegral ℤ (((t.den * n.den : ℕ) : D.host.K) * c) := by
    refine isIntegral_of_quadratic _ (t.num * n.den) (t.den ^ 2 * n.den * n.num) ?_
    push_cast
    rw [← et, ← en, ← ht, ← hn]
    ring
  exact ⟨⟨_, hi⟩, rfl⟩

end GlobalTheory.IntegralAtBothPrimes
end

