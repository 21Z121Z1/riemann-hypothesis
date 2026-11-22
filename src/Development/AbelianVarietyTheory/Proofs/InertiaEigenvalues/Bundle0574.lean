import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0294
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

theorem psi_alg_pt (a : Per.Ainf l) : psi bk (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

theorem gamma_acris0 (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (s : Per.Acris0 l) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      psi bk (s : Per.AinfP l) := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have hs : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (Per.Acris0 l) (Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (a : Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a))
    (hy : C.j (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) ∈ Per.FilP l m) :
    ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) ∈ Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : Per.Acris l) ^ N *
      (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z)) =
      ((l : ℕ) : Per.BdRp l) ^ N * algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l) +
      ((l : ℕ) : Per.BdRp l) ^ r * (((l : ℕ) : Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add, map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add, map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

theorem acris_dense {l : ℕ} [Fact l.Prime] (y : Per.Acris l) (r : ℕ) :
    ∃ (s : Per.Acris0 l) (z : Per.Acris l),
      y = algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : Per.Acris0 l)}) (Per.Acris0 l)))]
  exact h

theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l) (w : Per.AinfP l)
    (hw : ((l : ℕ) : Per.AinfP l) ^ N * (s : Per.AinfP l) +
      ((l : ℕ) : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) a =
        algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (Per.Ainf l) (Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s + ((l : ℕ) : Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add, gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisRegular
variable {l : ℕ} [Fact l.Prime] (C : Core l)

theorem exists_frob (C : Core l) :
    ∃ F : GQ l, ∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l := by
  obtain ⟨g, hg⟩ := FrobLaws.exists_ext C.σ
  refine ⟨g, fun ζ m hm hlm hζ => ?_⟩
  let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
  have := C.σ_root c m hm hlm (Subtype.ext hζ)
  rw [show ζ = (c : Om l) from rfl, hg, this]; rfl

theorem qB_coe (z : ℤ_[l]) : C.qB (z : ℚ_[l]) = Per.zB l z := (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z

theorem ι_aB (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, C.ι_j, GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap]
  simp only [aDp, RingHom.comp_apply]

theorem theta_eig {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) {g : GQ l} {x : ℚ_[l]}
    (hx : Per.σB g b = C.qB x * b) :
    Per.σC g (Per.θD l y) = algebraMap ℚ_[l] ℂ_[l] x * Per.θD l y := by
  have h1 := congrArg C.ι hx
  rw [(GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.1, map_mul, h, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1,
    show C.ι (C.qB x) = _ from C.ι_u _, ← map_mul] at h1
  have h2 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h1)
  rw [(thetaD_props l).2.2.2.2, map_mul, C.o_sec.th] at h2
  exact h2

theorem σB_tB (g : GQ l) : Per.σB g C.tB = C.qB ((C.χ g : ℤ_[l]) : ℚ_[l]) * C.tB := by
  rw [qB_coe, Core.tB, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, TAct.t_act l C g, map_mul,
    GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg]

theorem isUnit_of_theta {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) (hy : Per.θD l y ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate l _ hy fun g => (hb g).imp fun x hx => theta_eig C h hx
  obtain ⟨N, hN, hI⟩ := GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector l η _ hy hη
  obtain ⟨F, hF⟩ := exists_frob C
  obtain ⟨w, hw, hwI, hwF, hwφ⟩ := GlobalTheory.T.exists_unramified_period_ainf_unit l F hF (η F ^ N)⁻¹
  have h2 : C.ι (b ^ N * Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (y ^ N * aDp l w) := by
    rw [map_mul, map_pow, h, ι_aB, map_mul, map_pow]
  have hθ : Per.θD l (y ^ N * aDp l w) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hy) ((hw.map _).map _).ne_zero
  have hact : ∀ g : GQ l, Per.σC g (Per.θD l (y ^ N * aDp l w)) =
      algebraMap ℚ_[l] ℂ_[l] (((η g ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * Per.θD l y ^ N *
        Per.θD l (aDp l (Per.σA g w)) := by
    intro g
    rw [map_mul, map_mul, map_pow, map_pow, hη, ← (thetaD_props l).2.2.2.2,
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, mul_pow, ← map_pow, Units.val_pow_eq_pow_val,
      PadicInt.coe_pow]
  have hfix := GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius l F hF (Per.θD l (y ^ N * aDp l w))
    (fun g hg => by rw [hact, hI g hg, hwI g hg]; simp)
    (by
      rw [hact, hwF, map_mul, map_mul, ← C.o_sec.z, C.o_sec.th, map_mul, map_pow]
      have e : algebraMap ℚ_[l] ℂ_[l] (((η F ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
          algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
        rw [← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
      have e' : ((algebraMap ℚ_[l] (Om l) ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) : Om l) : ℂ_[l]) =
        algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
      rw [e']
      linear_combination (Per.θD l y ^ N * Per.θD l (aDp l w)) * e)
  have hinv : ∀ g : GQ l, Per.σB g (b ^ N * Per.aB l w) = b ^ N * Per.aB l w := by
    intro g
    obtain ⟨x, hx⟩ := hb g
    obtain ⟨z, hz⟩ := GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line l w _ hw hwφ g
    have e : Per.σB g (b ^ N * Per.aB l w) = C.qB (x ^ N * z) * (b ^ N * Per.aB l w) := by
      rw [map_mul, map_pow, hx, hz, map_mul, map_pow, qB_coe]
      ring
    have e2 := theta_eig C h2 e
    rw [hfix] at e2
    have e3 : algebraMap ℚ_[l] ℂ_[l] (x ^ N * z) = 1 := mul_right_cancel₀ hθ (by rw [one_mul, ← e2])
    have e4 : x ^ N * (z : ℚ_[l]) = 1 := (algebraMap ℚ_[l] ℂ_[l]).injective (by rw [e3, map_one])
    rw [e, e4, map_one, one_mul]
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified l C ⟨⊥, inferInstance⟩ _ fun g _ => hinv g
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, map_zero] at h2
    apply hθ
    rw [(BdRField.bdR_isField l).2.1 (h2.symm.trans (map_zero _).symm), map_zero]
  have hu : IsUnit (b ^ N * Per.aB l w) := hc ▸ (Ne.isUnit hc0).map C.u
  exact (isUnit_pow_iff hN.ne').1 (isUnit_of_mul_isUnit_left hu)

theorem isUnit_of_line (b : Per.Bcris l) (h0 : b ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨m, n, b', y, e, hy, hθ⟩ := GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero l C b h0
  have ht : IsUnit C.tB := (core_t_unit_fil l C).1
  have hu : IsUnit b' := isUnit_of_theta C hy hθ fun g => by
    obtain ⟨x, hx⟩ := hb g
    set a : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact PadicInt.coe_ne_zero.2 (C.χ g).ne_zero
    refine ⟨x * a ^ m * (a ^ n)⁻¹, ?_⟩
    have e1 := congrArg (Per.σB g) e
    rw [map_mul, map_mul, map_pow, map_pow, hx, σB_tB, ← ha] at e1
    have e2 : C.qB a ^ n * C.qB (a ^ n)⁻¹ = 1 := by
      rw [← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ ha0), map_one]
    apply (ht.pow n).mul_left_cancel
    rw [map_mul, map_mul, map_pow]
    linear_combination (-C.qB (a ^ n)⁻¹) * e1 + (C.qB x * C.qB a ^ m * C.qB (a ^ n)⁻¹) * e -
      (C.tB ^ n * Per.σB g b') * e2
  exact isUnit_of_mul_isUnit_left (e ▸ (ht.pow n).mul hu)

end GlobalTheory.MemLoc.CrisRegular

namespace GlobalTheory.MemLoc

theorem core_regular (l : ℕ) [Fact l.Prime] (C : Core l) : C.Regular :=
  GlobalTheory.T.bcris_regular_of_full_galois_line_units l C (CrisRegular.isUnit_of_line C)

theorem regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular :=
  fun l _ C _ => core_regular l C

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarevStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundModTwoUniformizerAtTwo_of_chebotarev : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  first | exact @GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis | exact GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis | (intros; apply GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA g) G → IsDiscMap WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  first | (exact @GlobalTheory.BSP.CocycleFrob.frob_eq) | (exact GlobalTheory.BSP.CocycleFrob.frob_eq) | (intros; apply GlobalTheory.BSP.CocycleFrob.frob_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (C : Wq l bk.a →+* bk.S) κ → ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ := by
  first | (exact @GlobalTheory.BSP.exists_const_add_X_mul_disc) | (exact GlobalTheory.BSP.exists_const_add_X_mul_disc) | (intros; apply GlobalTheory.BSP.exists_const_add_X_mul_disc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvPush

theorem c_mem_of_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (L : Ideal S) (i : ι) {x : A} (hx : x ∈ L.map s) : TB.c i x ∈ L := by
  have key : ∀ a : A, TB.c i (a * x) ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      rw [mul_comm, TB.c_mul]
      exact L.mul_mem_right _ hj
    | zero => intro a; rw [mul_zero, map_zero]; exact L.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add]; exact L.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem coeff_map {S A S' A' ι : Type} [CommRing S] [CommRing A] [CommRing S'] [CommRing A'] {s : S →+* A}
    {s' : S' →+* A'} {I : Ideal S} {I' : Ideal S'} (TB : TopBasis s I ι) (TB' : TopBasis s' I' ι) (g : S →+* S')
    (qf : A →+* A') (hq : ∀ y, qf (s y) = s' (g y)) (hb : ∀ i, qf (TB.b i) = TB'.b i) (hI : I.map g ≤ I')
    (hH : IsHausdorff I' S') (x : A) (α : ι) : TB'.c α (qf x) = g (TB.c α x) := by
  classical
  refine sub_eq_zero.1 (hH.haus _ fun n => SModEq.zero.2 ((Ideal.mul_top _).ge ?_))
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset ∪ {α} → TB.c i x ∈ I ^ n := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 h))
  have hm : qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i) ∈ (I' ^ n).map s' := by
    have h1 := Ideal.mem_map_of_mem qf (TB.approx x n _ hF)
    rw [Ideal.map_map, show qf.comp s = s'.comp g from RingHom.ext hq, ← Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.map_mono (Ideal.pow_right_mono hI n) h1
  have hc := c_mem_of_mem_map TB' _ α hm
  have e : TB'.c α (qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i)) =
      TB'.c α (qf x) - g (TB.c α x) := by
    rw [map_sub, map_sub, map_sum, map_sum, Finset.sum_eq_single α]
    · rw [map_mul, hq, hb, TB'.c_mul, TB'.c_self, mul_one]
    · intro i _ hi
      rw [map_mul, hq, hb, TB'.c_mul, TB'.c_ne α i (Ne.symm hi), mul_zero]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self α)) h
  rwa [e] at hc

end GlobalTheory.BSP.EnvPush

open GlobalTheory.BSP.EnvPush in

theorem GlobalTheory.BSP.envPush_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En An q hl hr x hx
  have hql : ∀ y : bk.prism.A, q.f (En.inl.f y) = An.inl.f (bk.ι.f y) := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hl
  have hqr : ∀ y : bk.prism.A, q.f (En.inr.f y) = An.inr.f y := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hr

  have hw : q.f En.w = An.w := by
    have e1 : q.f (En.inr.f (bk.toP X)) = An.inr.f (bk.toP X) := hqr _
    have e2 : En.inr.f (bk.toP X) = En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w := En.w_eq
    have e3 : An.inr.f (bk.toP X) = An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * An.w :=
      An.w_eq
    have e4 : q.f (En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w) =
        An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * q.f En.w :=
      (q.f.map_add _ _).trans (congrArg₂ (· + ·) (hql _) ((q.f.map_mul _ _).trans (congrArg (· * q.f En.w) (hql _))))
    have e5 := add_left_cancel (e4.symm.trans ((congrArg q.f e2).symm.trans (e1.trans e3)))
    have key : ∀ (b u v : An.Q.A), b ∈ nonZeroDivisors An.Q.A → b * u = b * v → u = v := fun b u v hb h =>
      sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).1 (by rw [mul_sub, h, sub_self]))
    have hnz : An.inl.f (bk.ι.f (bk.toP bk.E)) ∈ nonZeroDivisors An.Q.A :=
      (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk An.Q (An.inl.comp bk.ι) (An.inl.comp bk.ι)).1
    exact key _ _ _ hnz e5

  have hδ : ∀ (n : ℕ) (y : En.Q.A), q.f (En.Q.D.δ^[n] y) = An.Q.D.δ^[n] (q.f y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      exact (congrArg q.f (Function.iterate_succ_apply' _ n y)).trans ((q.f_δ _).trans
        ((congrArg An.Q.D.δ (ih y)).trans (Function.iterate_succ_apply' _ n _).symm))
  have hb : ∀ α, q.f (En.tb.b α) = An.tb.b α := by
    intro α
    refine (congrArg q.f (En.tb_b α)).trans ((map_finsuppProd q.f _ _).trans (Eq.trans ?_ (An.tb_b α).symm))
    exact Finsupp.prod_congr fun i _ =>
      (map_pow q.f _ _).trans (congrArg (· ^ α.1 i) ((hδ i En.w).trans (congrArg _ hw)))

  have hJ : (Ideal.span {((l : ℕ) : bk.prism.A)} ⊔ bk.prism.I).map bk.ι.f ≤
      Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I := by
    refine Ideal.map_le_iff_le_comap.2 (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
      fun y hy => Ideal.mem_sup_right (bk.ι.f_I y hy))
    show bk.ι.f ((l : ℕ) : bk.prism.A) ∈ Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I
    rw [map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I) (ainfObj K).A :=
    (ainfObj K).complete.toIsHausdorff

  have key : ∀ α, An.tb.c α (q.f x) = bk.ι.f (En.tb.c α x) := fun α =>
    coeff_map En.tb An.tb bk.ι.f q.f hql hb hJ hH x α

  obtain ⟨y, hy⟩ := hx
  have hl' : ∀ α, ((l : ℕ) : bk.S) ∣ En.tb.c α x := fun α => by
    apply (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.2
    refine ⟨An.tb.c α y, ?_⟩
    calc bk.ι.f (En.tb.c α x) = An.tb.c α (q.f x) := (key α).symm
      _ = An.tb.c α (An.inl.f ((l : ℕ) : (ainfObj K).A) * y) := by rw [hy, map_natCast]
      _ = ((l : ℕ) : (ainfObj K).A) * An.tb.c α y := An.tb.c_mul α _ y
  have h := (GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk En.Q.A (En.inl.f : bk.S →+* En.Q.A) (Digits l) En.tb ((l : ℕ) : bk.S) x).2 hl'
  have hg : ∀ {R A : Type} [CommRing R] [CommRing A] (s : R →+* A) (y : A) (n : ℕ), s n ∣ y → (n : A) ∣ y :=
    fun s y n h => (map_natCast s n) ▸ h
  exact hg _ _ _ h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∀ x, inclO l O (1 ⊗ₜ (muOf δ ^ β)) • I.ofT x ∈ MA P) ∧ (∀ v ∈ MA P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • v) = TWincl (inclO l O) T z) ∧ (∀ x, inclO l O (1 ⊗ₜ (muOf ε ^ β)) • I.ofT x ∈ LA t ϖ P) ∧ ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z := by
  first | exact @GlobalTheory.BKExp.exponents | exact GlobalTheory.BKExp.exponents | (intros; apply GlobalTheory.BKExp.exponents <;> assumption)
end

