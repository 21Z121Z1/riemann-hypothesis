import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatMove

variable {D : D7} (V : HSp D)

theorem mem_hat_iff (g : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V g ↔ ∃ z ∈ latGHat V 1, (finHom V g).1 *ᵥ z = w := by
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  have h2 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
  rw [h2, ← SetLike.mem_coe, h1]
  rfl

theorem mem_lat_iff (g : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V g ↔ finVec V v ∈ latGHat V g := by
  have h0 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  rw [← SetLike.mem_coe, h0, ← SetLike.mem_coe, h1]
  rfl

theorem fin_mul (g h : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ z = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem fin_one (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem move_mem (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V h) : (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  obtain ⟨z, hz, rfl⟩ := (mem_hat_iff V h w).1 hw
  exact (mem_hat_iff V _ _).2 ⟨z, hz, fin_mul V g h z⟩

theorem move_iff (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V h ↔ (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  refine ⟨move_mem V g h w, fun hw => ?_⟩
  have := move_mem V g⁻¹ _ _ hw
  rwa [← fin_mul, inv_mul_cancel, fin_one, inv_mul_cancel_left] at this

theorem lat_eq_of_hat_eq {h h' : GA D V} (e : latGHat V h = latGHat V h') : latG V h = latG V h' := by
  ext v
  rw [mem_lat_iff, mem_lat_iff, e]

theorem finCong_one {N : ℕ} {k : GA D V} (hk : FinCong V N k) : FinCong V 1 k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  exact ⟨N • y, AddSubgroup.nsmul_mem _ hy N, by rw [one_nsmul, e]⟩

theorem hat_eq_of_finCong {N : ℕ} {k : GA D V} (hk : FinCong V N k) : latGHat V k = latGHat V 1 := by
  have h1 := (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V k).1.2 (finCong_one V hk)
  have h2 : ∀ z ∈ latGHat V 1, (finHom V k⁻¹).1 *ᵥ z ∈ latGHat V 1 := by
    have hh := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
    rw [hh] at h1 ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latG V 1) (finHom V k) (cF D)
      (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1 h1 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).2.1
  ext w
  rw [mem_hat_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact h1 z hz
  · intro hw
    exact ⟨_, h2 w hw, by rw [← fin_mul, mul_inv_cancel, fin_one]⟩

end GlobalTheory.Member.LatMove

open GlobalTheory.Member.LatMove in

theorem GlobalTheory.Member.latG_move : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  intro D V
  refine ⟨fun γ γ' h hγ => ⟨fun v => ?_, fun w => move_iff V γ h w⟩, fun h h' e => ?_, fun N h k hk => ?_,
    fun h h' e => ?_⟩
  · rw [mem_lat_iff, mem_lat_iff, move_iff V γ h, ((GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V).2.2.2.2 γ γ' hγ).1 v]
  · have : latGHat V h = latGHat V h' := by
      ext w
      rw [mem_hat_iff V h, mem_hat_iff V h', e]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have : latGHat V (h * k) = latGHat V h := by
      ext w
      rw [move_iff V h⁻¹ (h * k), move_iff V h⁻¹ h, inv_mul_cancel_left, inv_mul_cancel,
        hat_eq_of_finCong V hk]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have e' : latGHat V h = latGHat V h' := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V h).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V h').2.2.2.2.1, e]
    refine (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V (h⁻¹ * h')).1.1 fun z hz => ?_
    have h1 := move_mem V h' 1 z hz
    rw [mul_one, ← e'] at h1
    have h2 := move_mem V h⁻¹ h _ h1
    rwa [← fin_mul, inv_mul_cancel] at h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatSelfDual

variable {D : D7}

theorem cF_eq_conj (D : D7) (x : D.host.E) : cF D x = D.host.conj x :=
  bridge_star_holds D.R D.host x

noncomputable def frameForm (V : HSp D) (v y : Fin V.rank → D.host.E) : D.host.E :=
  ∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)

theorem frameForm_smul_left (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (e • v) y = e * frameForm V v y := by
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_smul_right (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (e • y) = D.host.conj e * frameForm V v y := by
  rw [← cF_eq_conj]
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_add_left (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V (v + w) y = frameForm V v y + frameForm V w y := by
  simp only [frameForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem frameForm_add_right (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V v (w + y) = frameForm V v w + frameForm V v y := by
  simp only [frameForm, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem frameForm_int_smul_left (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (c • v) y = c • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c v, frameForm_smul_left, Algebra.smul_def]

theorem frameForm_int_smul_right (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (c • y) = (D.host.conj • c) • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c y, frameForm_smul_right, Algebra.smul_def, algebraMap_conj_smul]

theorem mem_iff_trace (D : D7) (z : D.host.E) :
    z ∈ D.host.AA * D.host.AAbar ↔
      ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  constructor
  · intro hz a
    have h : a • z ∈ NAA D := Submodule.smul_mem _ a hz
    rw [Algebra.smul_def] at h
    exact trace_int_of_mem hP D h
  · intro h
    have hz : D.host.xi0 * z ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mem_dual
        (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [FractionalIdeal.mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨n, hn⟩ := h c
      rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
      exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
    rw [← dual_eq hP D] at hz
    have h4 := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
        FractionalIdeal.spanSingleton_one, one_mul]
    rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  intro h
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem selfDual_one (V : HSp D) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V 1, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V 1 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  have hAb := AAbar_ne_zero D
  have hC : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, frameForm V v y ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V :=
    (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.2.2.2.2.2
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2]
  constructor
  · intro h
    have h5 : ∀ y0 ∈ latC V, frameForm V v y0 ∈ D.host.AA := by
      intro y0 hy0
      have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) *
          D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
        rw [FractionalIdeal.spanSingleton_mul_le_iff]
        intro b hb
        have := h (D.host.conj b • y0) (Submodule.subset_span ⟨_, conj_mem_AA D hb, y0, hy0, rfl⟩)
        rw [frameForm_smul_right, conj_conj, mul_comm b] at this
        exact this
      have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) ≤
          D.host.AA := by
        calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0)
            = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
                (frameForm V v y0) * D.host.AAbar) := by
              rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
          _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
          _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)
    have h6 : ∀ c ∈ D.host.AA⁻¹, c • v ∈ latC V := by
      intro c hc
      refine (hC _).1 fun y hy => ?_
      rw [frameForm_smul_left, ← inv_mul_cancel₀ hAA]
      exact FractionalIdeal.mul_mem_mul hc (h5 y hy)
    have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
      intro e he
      refine FractionalIdeal.mul_induction_on (C := fun e => e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x}) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
      · show (a * c) • v ∈ _
        rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • v, h6 c hc, rfl⟩
      · show (u + w) • v ∈ _
        rw [add_smul]; exact add_mem hu hw
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    rwa [one_smul] at this
  · intro hv w hw
    show frameForm V v w ∈ NAA D
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hv
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, hb, y, hy, rfl⟩ := hw
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((hC x).2 hx y hy)
        rw [frameForm_smul_left, frameForm_smul_right, ← hr, ← mul_assoc, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
      | zero => simp [frameForm]
      | add w w' _ _ h h' => rw [frameForm_add_right]; exact add_mem h h'
      | smul c w _ h => rw [frameForm_int_smul_right]; exact Submodule.smul_mem _ _ h
    | zero => simp [frameForm]
    | add v v' _ _ h h' => rw [frameForm_add_left]; exact add_mem h h'
    | smul c v _ h => rw [frameForm_int_smul_left]; exact Submodule.smul_mem _ _ h

theorem selfDual (V : HSp D) (g : GA D V) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V g, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V g := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg, hspan, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  have hlat := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E V.rank (latG V 1) (cF D) V.gramᵀ
    (D.host.AA * D.host.AAbar) (finHom V g) hfg hspan hcc hG hdet
    (mul_ne_zero (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (AAbar_ne_zero D))
    (selfDual_one V) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V g).1 v
  rw [← hlat] at key
  exact key

end GlobalTheory.Member.LatSelfDual

namespace GlobalTheory.Member

open LatSelfDual

theorem latG_selfDual : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  intro D V g J hJ
  subst hJ
  refine ⟨mem_iff_trace D, selfDual V g, fun v => ?_⟩
  have hcc := (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.1
  have hh : ∀ y, herm (-V.gramᵀ) v y = - frameForm V v y := by
    intro y
    simp only [herm, frameForm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  have ht : ∀ y, (∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * frameForm V v y) = n := by
    intro y
    rw [hh, neg_neg, mul_neg, map_neg]
    exact ⟨fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩,
      fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, hn]⟩⟩
  simp only [ht]
  rw [← selfDual V g v]
  constructor
  · intro h y hy
    refine (mem_iff_trace D _).2 fun a => ?_
    have h1 := h _ ((latG V g).smul_mem (D.host.conj⁻¹ • a) hy)
    rw [frameForm_int_smul_right, smul_inv_smul, Algebra.smul_def] at h1
    exact h1
  · intro h y hy
    exact trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (h y hy)

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicativeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  first | exact @GlobalTheory.Member.Arch.archM_spec | exact GlobalTheory.Member.Arch.archM_spec | (intros; apply GlobalTheory.Member.Arch.archM_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem map_span_eq_latG (D : D7) (V : HSp D) :
    (Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ V.L0, v = a • x}).map
      ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) = latG V 1 := by
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp⟩

theorem exists_iotaOK : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  intro D Q hP j hj
  obtain ⟨⟨-, hrt, hrt0, -⟩, -, -, hD⟩ := hP
  obtain ⟨hp, hq, φ, ε, hinj, hrange, hiso⟩ := hD j hj
  have hk := D.R.m_add_three_le_k
  obtain ⟨h1, h2⟩ := hj
  refine ⟨?_, ?_, hq, ?_⟩
  · let e := (((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E]
      (Fin (D.sp.W j).rank → D.host.E)).restrictScalars (𝓞 D.host.E))
    have hr : LinearMap.range (e ∘ₗ φ) = latG (D.sp.W j) 1 := by
      rw [LinearMap.range_comp, hrange]
      exact map_span_eq_latG D (D.sp.W j)
    have hspan : Submodule.span D.host.E (Set.range φ) = ⊤ := by
      have h := (GlobalTheory.T.adelicElementLattice_full_and_completion D (D.sp.W j) 1).2.1
      rw [← hr] at h
      have hs : ((LinearMap.range (e ∘ₗ φ) : Submodule _ _) : Set (Fin (D.sp.W j).rank → D.host.E)) =
          ((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E] (Fin (D.sp.W j).rank → D.host.E)) ''
            Set.range φ := by
        rw [← Set.range_comp]
        rfl
      rw [hs, ← Submodule.map_span] at h
      exact (Submodule.map_eq_top_iff (e := (D.sp.W j).frame.equivFun)).mp h
    have hε : ε = 1 := GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one D Q.H (Q.Dw j) j ⟨h1, h2⟩ hrt hrt0 hp hq φ ε hinj hspan hiso
    refine ⟨e ∘ₗ φ, hrt, hrt0, ⟨(D.sp.W j).frame.equivFun.injective.comp hinj, hr⟩, fun x y => ?_⟩
    have hx : ∀ z, (D.sp.W j).frame.equivFun.symm ((e ∘ₗ φ) z) = φ z := fun z =>
      (D.sp.W j).frame.equivFun.symm_apply_apply (φ z)
    rw [hx, hx, hiso x y, hε]
    simp
  · rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  · rw [hq]
    simp only [Ranks.sigW, Ranks.r]
    omega

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem isTypeFn_of_enum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem exists_openChart_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  intro hS E _ _ _ H Dw l Xo c z
  classical
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have htan : ∀ τ i, IsTanAt x (u τ i) := fun τ i => hb.1 _
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  have hb' : TanBasis x (fun j => u (e j).1 (e j).2) := by
    have : (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F := by
      funext j
      show (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hb
  have hbasis := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c R x u _ e htan heig).2 hb'
  obtain ⟨s, hsn⟩ := GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple E H Dw l Xo R x o.t m.toSABMap th hth
  have hgen := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hS E H Dw l Xo R x s hsn
  have hx : x ≫ Xo.s = sOf c R := by
    have h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (jR ≫ ·) pullback.condition
    rw [h1, hs, sOf]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let y : FrPt Xo c R := ⟨x, hx, u, htan, heig, hbasis, s, hgen⟩
  obtain ⟨p, ⟨f⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y
  have hiso : IsIso (spMap f.symm.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))
  refine ⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hy₀.1, Category.assoc]
  · rw [Category.assoc, hs]
    refine (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)
    ext a
    exact f.symm.commutes a
  · obtain ⟨q', hq'⟩ := (spMap f.symm.toAlgHom.toRingHom).surjective q
    exact ⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpenStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalLevel_subgroup_open : ∀ (D : D7) (V : HSp D), ∀ N : ℕ, (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧ (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) := by
  first | exact @GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | exact GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | (intros; apply GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds <;> assumption)
end

