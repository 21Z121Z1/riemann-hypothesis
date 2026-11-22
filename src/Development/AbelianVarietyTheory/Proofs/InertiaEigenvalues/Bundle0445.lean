import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.AntiRamConj GlobalTheory.AntiLAdic

namespace GlobalTheory.ConjPoly

theorem charpoly_smul_inv {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • N).charpoly = (m.map fun β => X - C (c * β⁻¹)).prod := by
  have hcard : Multiset.card m = n := by
    have := congrArg natDegree hM
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card, Fintype.card_fin] at this
    exact this.symm
  have ev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - M).det = (m.map fun β => y - β).prod := fun y => by
    rw [← Matrix.eval_charpoly, hM, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (-M).det = (m.map fun β => -β).prod := by simpa using ev 0
  have hne : (-M).det ≠ 0 := by
    intro e
    have : (-M * -N).det = 1 := by rw [neg_mul_neg, h, Matrix.det_one]
    rw [Matrix.det_mul, e, zero_mul] at this
    exact zero_ne_one this
  have hβ : ∀ β ∈ m, β ≠ 0 := by
    rintro β hβ rfl
    apply hne
    rw [h0]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨0, hβ, neg_zero⟩)
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono ?_)
  intro x hx
  have hx0 : x ≠ 0 := hx
  show eval x _ = eval x _
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have e1 : -M * (Matrix.scalar (Fin n) x - c • N) = x • (Matrix.scalar (Fin n) (c / x) - M) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal,
      mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, h, smul_sub, smul_smul, mul_div_cancel₀ _ hx0]
    simp
    abel
  rw [← Matrix.det_mul, e1, Matrix.det_smul, ev, h0, ← Multiset.prod_map_mul, Fintype.card_fin, ← hcard,
    ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun β hb => ?_
  have := hβ β hb
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  field_simp
  ring

theorem continuous_cyc_val (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous fun g : G F Ω => ((cyc F Ω l g : (Qbar l)ˣ) : Qbar l) := by
  have h1 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) := continuous_algebraMap _ _
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact h1.comp (h2.comp (Units.continuous_val.comp (continuous_cycZ F Ω l)))

theorem cyc_val_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cyc F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  rw [cyc_eq_map_cycZ, Units.coe_map, cycZ_of_isFrob hl h hσ]
  simp

theorem normV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : normV v ≠ 0 := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Nat.card_pos.ne'

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) : (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton, placesOver] using hv

theorem exists_conj (D : D7) : ∃ bar : PlE D.host → PlE D.host, Function.Injective bar ∧
    ∀ w, IsConjPl D.host w (bar w) ∧ normV (bar w) = normV w ∧ (IsSplitPl D.host w → IsSplitPl D.host (bar w)) := by
  choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv v).exists
  have hbb : ∀ v, bar (bar v) = v := fun v =>
    (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv (bar v)).unique (hbar _)
      (conjPl_symm (host_conj_conj D) (hbar v))
  have hc : ∀ v, IsConjPl D.host v (bar v) := fun v => (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).1 (hbar v)
  refine ⟨bar, Function.LeftInverse.injective hbb, fun w => ⟨hc w, normV_conjPl (hbar w), ?_⟩⟩
  rintro ⟨x, hx, hx'⟩
  let y : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x
  have hy : (y : D.host.E) = D.host.conj x := rfl
  refine ⟨y, (hc w x y hy).1 hx, fun z hz hzm => ?_⟩
  rw [hy, host_conj_conj] at hz
  have hzx : z = x := Subtype.ext hz
  rw [hzx] at hzm
  exact hx' y hy ((hc w y x (by rw [hy, host_conj_conj])).2 hzm)

theorem isoLoc_single (D : D7) (π : D.naut.CG D.R.r) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cpow_sq {q : ℂ} (hq : q ≠ 0) (s : ℝ) (k : ℤ) (h : (k : ℝ) = 2 * s) : q ^ k = q ^ (s : ℂ) * q ^ (s : ℂ) := by
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_intCast]
  congr 1
  rw [← two_mul]
  exact_mod_cast h

theorem charpoly_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc) (π : D.naut.CG D.R.r)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hπ : D.naut.csd π)
    (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    (((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i)).charpoly =
      ((((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)).charpoly := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  obtain ⟨hcont, -, hfr⟩ := hρ
  have hι := (iotaOQ_continuous_injective D i).1
  have hfr' := hinj.tendsto_cofinite.eventually hfr
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hall := (hfr.and hfr').and ((D.naut.locG_unr_ae π).and hl)
  refine charpoly_eq_of_dense (G D.host.E D.nd.Om) (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i))
    (fun g => (((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)) _ (hD _ (Filter.eventually_cofinite.1 hall))
    ((hcont.comp (continuous_conjHom D.ntw.cc hc)).matrix_map hι)
    (((continuous_cyc_val D.host.E D.nd.Om (D.nd.l i)).zpow₀ (1 - (D.R.r : ℤ))
      fun g => Or.inl (Units.ne_zero _)).fun_smul ((hcont.comp continuous_inv).matrix_map hι)) ?_ g
  rintro σ ⟨w, hw, -, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu, hwl⟩ := not_not.1 hw
  obtain ⟨hcj, hn, -⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr π w (bar w) hπ hcj hu
  have e1 := h1 B σ hB hσ
  have e2 := h2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  have e3 := charpoly_smul_inv _
    (((ρ σ⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
    (by rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]) _ (((normV w : ℕ) : ℂ) ^ (1 - (D.R.r : ℤ))) e1
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  beta_reduce
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, cyc_val_frob hwl hB hσ]
  refine e2.trans (Eq.trans ?_ (e3.symm.trans ?_))
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    rw [cpow_sq hq ((1 - (D.R.r : ℝ)) / 2) _ (by push_cast; ring)]
    have : ((normV w : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by
      simp [hq]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right₀ this, mul_comm a⁻¹]
  · congr 1
    ext a b
    simp [iotaO, iotaOQ]

theorem chi_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    iotaOQ D.nd D.naut i (D.nd.chi i 1 (conjHom D.ntw.cc hc g) : (D.nd.O i)ˣ) *
        iotaOQ D.nd D.naut i (D.nd.chi i 1 g : (D.nd.O i)ˣ) =
      ((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ ((D.R.t : ℤ) - (D.R.nV : ℤ)) := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  have hι := (iotaOQ_continuous_injective D i).1
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hout : ∀ᶠ w in Filter.cofinite, w ∉ placesOver D.host.E (D.nd.l i) ∧ w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
    Filter.Eventually.and hl ((D.nd.S i).eventually_cofinite_notMem.and (D.nd.Q i).eventually_cofinite_notMem)
  have hall := (hout.and (hinj.tendsto_cofinite.eventually hout)).and (D.naut.locG_unr_ae (D.naut.muC i))
  have hχ := hι.comp (D.nd.chi_cont i 1)
  refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
    ((hχ.comp (continuous_conjHom D.ntw.cc hc)).mul hχ)
    ((continuous_cyc_val _ _ _).zpow₀ _ fun g => Or.inl (Units.ne_zero _)) ?_) g
  rintro σ ⟨w, hw, hs, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu⟩ := not_not.1 hw
  obtain ⟨hcj, hn, hs'⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr _ w (bar w) (D.naut.muC_csd i) hcj hu
  obtain ⟨u1, e1⟩ := D.naut.chi_mu i w ⟨hs, h1⟩
  obtain ⟨u2, e2⟩ := D.naut.chi_mu i (bar w) ⟨hs' hs, h2⟩
  have e1 := e1 B σ hB hσ
  have e2 := e2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  have one : ∀ (χ : D.naut.CG 1) (v : PlE D.host), D.naut.unr (D.naut.locG χ v) →
      ∃ a, D.naut.frobEig (D.naut.locG χ v) = {a} := fun χ v h =>
    Multiset.card_eq_one.1 ((D.naut.frobEig_card _ h).trans (D.naut.locG_dim χ v))
  obtain ⟨a, ha⟩ := one _ w (D.naut.etaT_unr w)
  obtain ⟨b, hb⟩ := one _ (bar w) (D.naut.etaT_unr (bar w))
  obtain ⟨m, hm⟩ := one _ w hu
  have hab := D.naut.etaT_split w (bar w) hs hcj a b ha hb
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact D.naut.frobEig_ne_zero _ hu (by rw [hm]; exact Multiset.mem_singleton_self _)
  obtain ⟨v1, f1⟩ := D.naut.etaTinv_def w
  obtain ⟨v2, f2⟩ := D.naut.etaTinv_def (bar w)
  rw [ha, Multiset.map_singleton] at f1
  rw [hb, Multiset.map_singleton] at f2
  rw [D.naut.frobEig_tw _ _ u1, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu v1 (D.naut.locG_dim _ _) f1, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e1
  rw [D.naut.frobEig_tw _ _ u2, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu' v2 (D.naut.locG_dim _ _) f2, he, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj, hn] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  apply (D.naut.iotaQC i).injective
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [map_mul, cyc_val_frob h1.1 hB hσ, map_zpow₀, map_natCast,
    cpow_sq hq (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) _ (by push_cast; ring)]
  refine (congrArg₂ (· * ·) e2.symm e1.symm).trans ?_
  have hab' : a⁻¹ * b⁻¹ = 1 := by rw [← mul_inv, hab, inv_one]
  have hmm : m⁻¹ * m = 1 := inv_mul_cancel₀ hm0
  generalize ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = y
  calc m⁻¹ * b⁻¹ * y * (m * a⁻¹ * y) = (m⁻¹ * m) * (a⁻¹ * b⁻¹) * (y * y) := by ring
    _ = y * y := by rw [hmm, hab', one_mul, one_mul]

theorem conj_inertia : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  intro D hD i π ρ hπ hρ w B hw hB s hs s' hs'
  have hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
    fun x => ⟨_, cc_symm_algebraMap_host D x⟩
  obtain rfl : s' = conjHom D.ntw.cc hc s := by
    ext y
    rw [conjHom_apply, ← hs', RingEquiv.apply_symm_apply]
  have hε : cyc D.host.E D.nd.Om (D.nd.l i) s = 1 := cyc_eq_one_of_mem_Ine hw hB hs
  have hι := (iotaOQ_continuous_injective D i).2
  constructor
  · have h := charpoly_conj D hD i π ρ hπ hρ hc s
    rw [hε, Units.val_one, one_zpow, one_smul, Matrix.charpoly_map, Matrix.charpoly_map] at h
    exact Polynomial.map_injective _ hι h
  · have h := chi_conj D hD i hc s
    rw [hε, Units.val_one, one_zpow, ← map_mul, ← map_one (iotaOQ D.nd D.naut i), ← Units.val_mul] at h
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left (Units.ext (hι h))

end GlobalTheory.ConjPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharValueLength

variable {l : ℕ} [Fact l.Prime] in
private theorem isUnit_of_toZMod_ne_zero' {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hx

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_prime_eq_one_add_pow_succ {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (h2 : l = 2 → 2 ≤ r) (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ l = 1 + (l : ℤ_[l]) ^ (r + 1) * w' := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  set x := (l : ℤ_[l]) ^ r * w with hx
  have hexp : u ^ l = (∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l])) + x * l + 1 := by
    rw [hu, add_comm, add_pow, show l + 1 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, zero_add]
  have hdvd : (l : ℤ_[l]) ^ (r + 2) ∣ ∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j + 2 ≤ l := by rw [Finset.mem_range] at hj; omega
    have hxp : x ^ (j + 1 + 1) = (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * w ^ (j + 1 + 1) := by
      rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (j + 2) l with hlt | hge
    · have hc : (l : ℤ_[l]) ∣ ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) :=
        Nat.cast_dvd_cast ((Fact.out : l.Prime).dvd_choose_self (by omega) (by omega))
      have h1 : (l : ℤ_[l]) ^ (r + 2) ∣ (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * l := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      exact h1.trans (mul_dvd_mul (Dvd.intro _ hxp.symm) hc)
    · have hle : r + 2 ≤ r * (j + 1 + 1) := by
        rcases Nat.lt_or_ge l 3 with h | h
        · have := h2 (by omega); nlinarith
        · nlinarith
      exact ((pow_dvd_pow _ hle).trans (Dvd.intro _ hxp.symm)).mul_right _
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨w + l * c, isUnit_of_toZMod_ne_zero' ?_, ?_⟩
  · simpa [ZMod.natCast_self] using (hw.map PadicInt.toZMod).ne_zero
  · rw [hexp, hc, hx]; ring

variable {l : ℕ} [Fact l.Prime] in
private theorem toZMod_principalUnit_eq_one {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (hu : u = 1 + (l : ℤ_[l]) ^ r * w) : PadicInt.toZMod u = 1 := by
  rw [hu]
  simp [ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.1 hr)]

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_of_not_dvd {u w : ℤ_[l]} {r m : ℕ} (hr : 1 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) (hm : ¬ l ∣ m) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ m = 1 + (l : ℤ_[l]) ^ r * w' := by
  refine ⟨w * ∑ i ∈ Finset.range m, u ^ i, hw.mul (isUnit_of_toZMod_ne_zero' ?_), ?_⟩
  · rw [map_sum]
    simp only [map_pow, toZMod_principalUnit_eq_one hr hu, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact fun h => hm ((ZMod.natCast_eq_zero_iff m l).1 h)
  · have hg := geom_sum_mul u m
    have hu1 : u - 1 = (l : ℤ_[l]) ^ r * w := by rw [hu]; ring
    rw [hu1] at hg
    linear_combination -hg

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_eq_one_add_pow_add_padicValNat {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r) (h2 : l = 2 → 2 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) {k : ℕ} (hk : k ≠ 0) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ k = 1 + (l : ℤ_[l]) ^ (r + padicValNat l k) * w' := by
  have hpow : ∀ a : ℕ, ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ (l ^ a) = 1 + (l : ℤ_[l]) ^ (r + a) * w' := by
    intro a
    induction a with
    | zero => exact ⟨w, hw, by simpa using hu⟩
    | succ a ih =>
      obtain ⟨w', hw', h'⟩ := ih
      obtain ⟨w'', hw'', h''⟩ :=
        principalUnit_pow_prime_eq_one_add_pow_succ (by omega) (fun h => by have := h2 h; omega) hw' h'
      exact ⟨w'', hw'', by rw [pow_succ, pow_mul, h'', ← add_assoc]⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk l (Fact.out : l.Prime).one_lt.ne'
  obtain ⟨w', hw', h'⟩ := hpow a
  obtain ⟨w'', hw'', h''⟩ := principalUnit_pow_of_not_dvd (by omega) hw' h' hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  refine ⟨w'', hw'', ?_⟩
  rw [padicValNat.mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, pow_mul, h'']

private theorem length_quotient_span_unit_mul_pow_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (w : Oˣ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {(w : O) * ϖ ^ n}) = n := by
  rw [Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n

theorem _root_.GlobalTheory.CharValueLength.injOn_and_lenUnit : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ _root_.Formalism.BasicNotions.lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  intro l _ O _ _ _ _ _ _ s t u v χ hs hs2 huv hχ
  have hl0 : (l : O) ≠ 0 := _root_.GlobalTheory.LenUnitPow.natCast_ne_zero l
  have hD : ∀ k : ℕ, k ≠ 0 → ∃ ε : Oˣ,
      algebraMap ℤ_[l] O u ^ k - 1 = ε * (l : O) ^ (s + padicValNat l k) := by
    intro k hk
    obtain ⟨w', hw', h'⟩ := principalUnit_pow_eq_one_add_pow_add_padicValNat hs hs2 v.isUnit huv hk
    refine ⟨(hw'.map (algebraMap ℤ_[l] O)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, h', map_add, map_one, map_mul, map_pow, map_natCast]
    ring
  have hrel : ∀ c, 1 ≤ c → c ≤ t → (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) = χ 1 := by
    intro c h1 h2
    have h : χ c * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (c - 1) = χ 1 := by
      rw [hχ c h1 h2, mul_assoc, ← zpow_natCast, ← zpow_add, Nat.cast_sub h1, Nat.cast_one,
        neg_add_cancel, zpow_zero, mul_one]
    have h' := congrArg (fun z : Oˣ => (z : O)) h
    simpa using h'
  have hφu : IsUnit (algebraMap ℤ_[l] O u) := u.isUnit.map _
  constructor
  · intro c hc c' hc' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hc hc'
    simp only at heq
    have key : ∀ a b : ℕ, 1 ≤ a ∧ a ≤ t → 1 ≤ b ∧ b ≤ t → (χ a : O) = χ b → a ≤ b → a = b := by
      intro c c' hc hc' heq hle
      by_contra hne
      obtain ⟨ε, hε⟩ := hD (c' - c) (by omega)
      have e1 := hrel c hc.1 hc.2
      have e2 := hrel c' hc'.1 hc'.2
      rw [← heq, show c' - 1 = (c - 1) + (c' - c) by omega, pow_add] at e2
      have h0 : (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) *
          (algebraMap ℤ_[l] O u ^ (c' - c) - 1) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · exact ((χ c).isUnit.mul (hφu.pow _)).ne_zero h
      · rw [hε] at h
        exact mul_ne_zero ε.ne_zero (pow_ne_zero _ hl0) h
    rcases le_total c c' with hle | hle
    · exact key c c' hc hc' heq hle
    · exact (key c' c hc' hc heq.symm hle).symm
  · have hterm : ∀ c ∈ Finset.Ioc 1 t, ∃ ε : Oˣ,
        (χ 1 : O) - χ c = ε * (l : O) ^ (s + padicValNat l (c - 1)) := by
      intro c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨ε, hε⟩ := hD (c - 1) (by omega)
      refine ⟨χ c * ε, ?_⟩
      rw [← hrel c (by omega) hc.2, Units.val_mul, mul_assoc, ← hε]
      ring
    choose! ε hε using hterm
    have hprod : ∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - χ c) =
        ((∏ c ∈ Finset.Ioc 1 t, ε c : Oˣ) : O) *
          (l : O) ^ (∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1))) := by
      rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Units.coe_prod]
    have hsum : ∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1)) =
        ∑ k ∈ Finset.Ioo 0 t, (s + padicValNat l k) := by
      refine Finset.sum_nbij' (fun c => c - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
        simp only [Finset.mem_Ioc, Finset.mem_Ioo] at ha ⊢ <;> omega
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    have he : e ≠ 0 := by
      rintro rfl
      exact _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit l (O := O)
        (by rw [hη, pow_zero, mul_one]; exact η.isUnit)
    unfold _root_.Formalism.BasicNotions.lenUnit
    rw [hprod, hsum, hη, mul_pow, ← pow_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, length_quotient_span_unit_mul_pow_eq hϖ, length_quotient_span_unit_mul_pow_eq hϖ,
      ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 he)]
    push_cast
    rfl

end GlobalTheory.CharValueLength
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactAdelicUnitriangularEntriesMemCompactStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  first | exact @GlobalTheory.CellDec.isCompact_unip_entries_mem | exact GlobalTheory.CellDec.isCompact_unip_entries_mem | (intros; apply GlobalTheory.CellDec.isCompact_unip_entries_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.CrysCoef

open Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {L L' : Type} [Field L] [Algebra Qp L] [Field L'] [Algebra Qp L']

theorem isCrys_mapM [Algebra L L'] [IsScalarTower Qp L L'] [FiniteDimensional L L']
    {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) L) (h : IsCrys PD (matRep M)) :
    IsCrys PD (matRep (mapM (algebraMap L L') M)) := by
  let e := Module.finBasis L L'
  let E : (Fin k → L') ≃ₗ[L] (Fin (finrank L L') → Fin k → L) :=
    { toFun := fun v j i => e.repr (v i) j
      invFun := fun w i => e.equivFun.symm fun j => w j i
      map_add' := fun x y => by funext j i; simp
      map_smul' := fun c x => by funext j i; simp
      left_inv := fun v => by
        funext i
        exact e.equivFun.symm_apply_apply (v i)
      right_inv := fun w => by
        funext j i
        exact congrFun (e.equivFun.apply_symm_apply fun j => w j i) j }
  have : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine GlobalTheory.CoeffExt.isCrys_ext PD (E := E) (fun g x j => ?_) (Fintype.card_fin _).symm h
  funext i
  change e.repr (∑ a, algebraMap L L' (M g i a) * x a) j = ∑ a, M g i a * e.repr (x a) j
  simp only [← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

end Generic

theorem isCrys_inclusion (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L L' : FinExt l) (h : L.1 ≤ L'.1) (k : ℕ)
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥L.1) (hM : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep (mapM (IntermediateField.inclusion h).toRingHom M)) := by
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 ↥L'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion h).commutes x).symm
  haveI := L'.2
  haveI : FiniteDimensional ↥L.1 ↥L'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  exact isCrys_mapM (P.PD K) M hM

end GlobalTheory.CrysCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSetStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  first | exact @GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | exact GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | (intros; apply GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlace_of_over_type_prime : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  first | exact @GlobalTheory.TypeSplit.main | exact GlobalTheory.TypeSplit.main | (intros; apply GlobalTheory.TypeSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsDictionaryAtEmbeddingOverRealPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D → GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool), (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ, (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧ (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) = {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  first | exact @GlobalTheory.JumpDictRec.main | exact GlobalTheory.JumpDictRec.main | (intros; apply GlobalTheory.JumpDictRec.main <;> assumption)
end

