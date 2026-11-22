import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.EpsInertia

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem mem_GK (σ : GQ l) (h : ∀ x : E, σ (Bw.j (algebraMap E Ω x)) = Bw.j (algebraMap E Ω x)) :
    σ ∈ GK Bw.Kw := by
  have hc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun x => (spectralNorm_eq_of_equiv σ x).symm).continuous
  rintro ⟨x, hx⟩
  have hcl : closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {y | σ y = y} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact h y) (isClosed_eq hc continuous_id)
  exact hcl (Bw.j_dense hx)

theorem cycZ_bridge [IsAlgClosed Ω] (g : ↥Gw) :
    cycZ E Ω l (g : Ω ≃ₐ[E] Ω) = cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := Bw.j.charZero
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective Bw.j.injective
  have ha : (g : Ω ≃ₐ[E] Ω) ζ =
      ζ ^ (((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω (g : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one
  have hb : ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) (Bw.j ζ) = Bw.j ζ ^
      (((cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut (GQ l) (Om l) ((Bw.e g : ↥(GK Bw.Kw)) : GQ l)) _ hζ'.pow_eq_one
  rw [Bw.e_comm, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

end Bridge

theorem fix_roots {l : ℕ} [Fact l.Prime] (σ : GQ l) (s : ℕ) (z : ℤ_[l])
    (h : ((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * z) (y : Om l)
    (hy : y ^ l ^ s = 1) : σ y = y := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hb : σ y = y ^ (((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow s).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) _ hy
  have h0 : ((l : ZMod (l ^ s))) ^ s = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h, map_add, map_one, map_mul, map_pow, map_natCast, h0, zero_mul, add_zero, ZMod.val_one_eq_one_mod] at hb
  rw [hb, ← pow_eq_pow_mod 1 hy, pow_one]

theorem epsAll : ∀ (D : D7) (i : D.nd.Loc), EpsAll D i := by
  intro D i w hw z
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hs : D.nd.s0 i ≠ 0 := by
    have := UpperTheory.KStar.S0.one_le_localLevel D.nd i
    omega
  have hu : IsUnit (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z) := by
    rw [← sub_neg_eq_add]
    refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
    have h1 := (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    exact PadicInt.irreducible_p.not_isUnit h1
  obtain ⟨u, hu⟩ := hu
  obtain ⟨σ, hσK, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ GK (D.nbr i w hw).Kw := by
    refine mem_GK _ σ fun x => ?_
    have hle : MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i]
        {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      have hm : ∀ y, σ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := fun y hy => by
        rintro ⟨_, k, rfl⟩
        exact (MulAction.stabilizer (GQ (D.nd.l i)) y).zpow_mem hy k
      refine sup_le (fun y hy => hm y (hσK y hy)) (IntermediateField.adjoin_le_iff.2 fun y hy => hm y ?_)
      exact fix_roots σ _ z (by rw [hσu, hu]) y hy
    exact hle (GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity D i w hw x) ⟨σ, Subgroup.mem_zpowers σ⟩
  set g := (D.nbr i w hw).e.symm ⟨σ, hσ⟩ with hg
  have he : (((D.nbr i w hw).e g : ↥(GK (D.nbr i w hw).Kw)) : GQ (D.nd.l i)) = σ := by
    rw [hg, MulEquiv.apply_symm_apply]
  refine ⟨g.1, ⟨g.2, fun x hx => ?_⟩, by rw [cycZ_bridge (D.nbr i w hw) g, he, hσu, hu]⟩
  have h1 := GlobalTheory.UnramInertia.norm_sub_lt_one_of_fix _ σ hσK _
    ((D.nbr_ind i w hw x).1 (((D.nd.plOm.1 w).valuation_le_one_iff x).1 hx))
  rw [← he, (D.nbr i w hw).e_comm, ← map_sub] at h1
  set y := g.1 x - x
  by_cases hy : y = 0
  · rw [hy, map_zero]; exact zero_lt_one
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, h, not_le]
  exact h1

end GlobalTheory.EpsInertia

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeight
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finset_sum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_difference_ideal_power_mem : ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u → q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B), (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  first | exact @GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | exact GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | (intros; apply GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section SdClosed

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem lTo0_atTop {w : ℕ → Wq l a} : LTo0 l w ↔ ∀ r : ℕ, ∃ N, ∀ n ≥ N, (l : Wq l a) ^ r ∣ w n := by
  simp only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]

theorem sdSet_zero : (0 : ZMod a → K⟦X⟧) ∈ SdSet t K e :=
  ⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩

theorem sdSet_one : (1 : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩
  · rw [if_neg (by omega)]; exact dvd_zero _
  · rw [Pi.one_apply, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sdSet_neg {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : -F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩
  · simpa using hn
  · simp [hF τ n]

theorem sdSet_add {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F + G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩
  · exact dvd_add hn.1 hn.2
  · simp [mul_add, hF τ n, hG τ n]

theorem fact_div_dvd (e i j : ℕ) : (i / e).factorial * (j / e).factorial ∣ ((i + j) / e).factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))

theorem sdSet_mul {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F * G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let q : ℕ → ℕ → ℕ := fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)
  have hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial) := fun i j =>
    (Nat.div_mul_cancel (fact_div_dvd e i j)).symm
  refine ⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩
  · rw [lTo0_atTop] at hw hw' ⊢
    intro r
    obtain ⟨N, hN⟩ := hw r
    obtain ⟨N', hN'⟩ := hw' r
    refine ⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [nsmul_eq_mul]
    apply Dvd.dvd.mul_left
    by_cases h1 : N ≤ p.1
    · exact (hN _ h1).mul_right _
    · exact (hN' _ (by omega)).mul_left _
  · rw [Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]
    push_cast
    ring

theorem sd_sub_sdSet : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  let S : Subring (ZMod a → K⟦X⟧) :=
    { carrier := SdSet t K e
      zero_mem' := sdSet_zero t e
      one_mem' := sdSet_one t e
      add_mem' := fun hF hG => sdSet_add t e hF hG
      mul_mem' := fun hF hG => sdSet_mul t e hF hG
      neg_mem' := fun hF => sdSet_neg t e hF }
  intro F hF
  exact (Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF

end SdClosed

theorem sdSet_closed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact sd_sub_sdSet t e

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section Closed

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a]

theorem LTo0_zero {ι : Type} : LTo0 l (0 : ι → Wq l a) :=
  fun _ => Eventually.of_forall fun _ => dvd_zero _

theorem LTo0_add {ι : Type} {w w' : ι → Wq l a} (h : LTo0 l w) (h' : LTo0 l w') : LTo0 l (w + w') :=
  fun r => ((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2

theorem LTo0_neg {ι : Type} {w : ι → Wq l a} (h : LTo0 l w) : LTo0 l (-w) :=
  fun r => (h r).mono fun _ hp => (dvd_neg).2 hp

theorem LTo0_single : LTo0 l (fun p : ℕ × ℕ => if p = (0, 0) then (1 : Wq l a) else 0) :=
  fun _ => (eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]

theorem LTo0_conv {w w' : ℕ × ℕ → Wq l a} (h : LTo0 l w) (h' : LTo0 l w')
    (c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ) :
    LTo0 l (fun p : ℕ × ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (c p.1 p.2 x y : Wq l a) * w (x.1, y.1) * w' (x.2, y.2)) := by
  intro r
  have hB := h r
  have hB' := h' r
  rw [Filter.eventually_cofinite] at hB hB' ⊢
  refine ((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_
  rintro ⟨i, n⟩ hp
  by_contra hni
  apply hp
  refine Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_
  by_cases h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _
  by_cases h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)
  · exact dvd_mul_of_dvd_right h2 _
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  exact (hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem PPSet_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e :=
  ⟨0, LTo0_zero, fun τ i n => by simp⟩

theorem PPSet_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e := by
  refine ⟨_, LTo0_single, fun τ i n => ?_⟩
  simp only [Pi.one_apply, coeff_one]
  by_cases hi : i = 0
  · subst hi
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp [hi]

theorem PPSet_add {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F + G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩
  simp only [Pi.add_apply, map_add, mul_add, hF, hG]

theorem PPSet_neg {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : -F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, LTo0_neg hw, fun τ i n => ?_⟩
  simp only [Pi.neg_apply, map_neg, mul_neg, hF]

theorem PPSet_mul {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F * G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ := fun i n x y =>
    (i.factorial * (n / e).factorial) /
      ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))
  refine ⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩
  have hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      i.factorial * (n / e).factorial =
        c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial)) := by
    intro x hx y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    refine (Nat.div_mul_cancel ?_).symm
    rw [mul_mul_mul_comm]
    apply mul_dvd_mul
    · rw [← hx]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
        (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))
  simp only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]
  push_cast
  ring

theorem PPd_subset_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  let S : Subring (ZMod a → K⟦X⟧⟦X⟧) :=
    { carrier := PPSet t K e
      mul_mem' := PPSet_mul t e
      one_mem' := PPSet_one t e
      add_mem' := PPSet_add t e
      zero_mem' := PPSet_zero t e
      neg_mem' := PPSet_neg t e }
  exact (Subring.closure_le (t := S)).2 le_rfl hF

end Closed

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProofStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof : StepJumpDual := by
  first | exact @GlobalTheory.Pass.JumpDualStep.jumpDual_main | exact GlobalTheory.Pass.JumpDualStep.jumpDual_main | (intros; apply GlobalTheory.Pass.JumpDualStep.jumpDual_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearODStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_approx_toOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O), (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) → ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  first | exact @GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | exact GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | (intros; apply GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKGal
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing : ∀ (l : ℕ) [Fact l.Prime] (ε : OCb l), IsEps ε → ∀ a : Ainf l, (∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0) → (ε - 1) ∣ a.coeff 0 := by
  first | exact @GlobalTheory.eps_sub_one_dvd_coeff_zero | exact GlobalTheory.eps_sub_one_dvd_coeff_zero | (intros; apply GlobalTheory.eps_sub_one_dvd_coeff_zero <;> assumption)
end

