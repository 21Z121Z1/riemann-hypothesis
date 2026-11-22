import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEeVOfCapelli
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StandardKTypeOfCentralChar
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem scalar_genSub {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (A : Module.End ℂ M) (hA : ∀ a b, Commute (E a b) A) (c : ℂ) (V : Submodule ℂ M)
    (hV : ∀ y ∈ V, A y = c • y) : ∀ y ∈ genSub E V, A y = c • y := by
  intro y hy
  have hle : genSub E V ≤ LinearMap.ker (A - c • (1 : Module.End ℂ M)) := by
    refine sInf_le ⟨fun v hv => ?_, fun a b v hv => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hV v hv,
        sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
      rw [← Module.End.mul_apply, ← (hA a b).eq, Module.End.mul_apply, sub_eq_zero.1 hv, map_smul,
        sub_self]
  have hy' := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at hy'
  exact hy'

theorem standardKType_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : LowestKTypeEulerTensorStandard n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq f hf

  have hcV : ∀ ω : ℂ, ∀ y ∈ V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y :=
    fun ω y hy => hcV_of_centralChar n hCC ε lam h H σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  exact prodShift_eeV_of_capelli' E hD.glRep (thV lam) (genSub E V)
    (fun ω => scalar_genSub E _ (fun a b => Capelli.capelliC_central E hD.glRep ω a b) _ V (hcV ω)) f hf

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

theorem vc_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vc_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensV_apply, vc_tensV_apply, map_add]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensVd_apply, vc_tensVd_apply, map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.WeightVectorTensorEqDual
section
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lamd (lam : Fin n → ℝ) : Fin n → ℝ := fun a => -lam (Fin.rev a)

theorem card_eq_of_rev (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ b, P b ↔ Q (Fin.rev b)) : (univ.filter P).card = (univ.filter Q).card := by
  apply Finset.card_bij' (fun b _ => Fin.rev b) (fun b _ => Fin.rev b) <;> simp [h]

theorem rhoN_rev (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoN
  rw [h1, h2]
  ring

theorem rhoC_rev (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoC
  rw [h1, h2]
  ring

theorem lowK_rev (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK (ε ∘ Fin.rev) (lamd lam) a = -lowK ε lam (Fin.rev a) := by
  simp only [lowK, Pi.add_apply, Pi.sub_apply, lamd, rhoN_rev, rhoC_rev]
  ring

theorem casVal_rev (lam : Fin n → ℝ) : casVal (lamd lam) = casVal lam := by
  unfold casVal nsq dot
  simp only [lamd, neg_mul_neg]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun a => lam a * lam a)

theorem pOf_rev (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem qOf_rev (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem hNeed_rev (ε : Fin n → Bool) : hNeed (ε ∘ Fin.rev) = hNeed ε := by
  unfold hNeed; rw [pOf_rev, qOf_rev]

theorem gapLap_rev {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (lamd lam) h := by
  obtain ⟨hanti, hgap, hh⟩ := hg
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a b hab => ?_, by rwa [hNeed_rev]⟩
  have := hgap (Fin.rev a) (Fin.rev b) hab
  rw [show lamd lam a - lamd lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) by simp only [lamd]; ring, abs_neg]
  exact this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def cjV (V : Submodule ℂ D) : Submodule ℂ (cjSub D) := V.map (ofDL (D := D))

theorem mem_cjV {V : Submodule ℂ D} (x : cjSub D) : x ∈ cjV V ↔ toD x ∈ V := by
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro h; exact ⟨toD x, h, rfl⟩

theorem ofD_E (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    ofD (E a b u) = (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) • Edd ε E (Fin.rev b) (Fin.rev a) (ofD u) := by
  rw [Edd_ofD, smul_ofD, Fin.rev_rev, Fin.rev_rev, smul_smul]
  have h1 : conj (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) = 1 := by
    simp only [map_neg, map_mul, conj_sg]
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem kirr_cjV {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    IsKIrrHW (ε ∘ Fin.rev) (Edd ε E) (lowK (ε ∘ Fin.rev) (lamd lam)) (cjV V) := by
  obtain ⟨hfin, hst, hirr, w, hwV, hw0, hwa, hwb⟩ := hV
  refine ⟨?_, ?_, ?_, ofD w, (mem_cjV _).2 hwV, ?_, ?_, ?_⟩
  · have hfg : V.FG := Module.Finite.iff_fg.mp hfin
    exact Module.Finite.iff_fg.mpr (hfg.map _)
  · intro a b hab v hv
    rw [mem_cjV] at hv ⊢
    exact V.smul_mem _ (hst (Fin.rev b) (Fin.rev a) hab.symm _ hv)
  · intro S' hle hS'
    have hSle : S'.comap (ofDL (D := D)) ≤ V := fun u hu => (mem_cjV (ofD u)).1 (hle hu)
    have hSst : IsKStableSub ε E (S'.comap (ofDL (D := D))) := by
      intro a b hab u hu
      show ofD (E a b u) ∈ S'
      rw [ofD_E ε E a b u]
      refine S'.smul_mem _ (hS' _ _ ?_ _ hu)
      simp [hab]
    rcases hirr _ hSle hSst with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : toD x ∈ S'.comap (ofDL (D := D)) := hx
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← ofD_toD x, this]
      rfl
    · right
      refine le_antisymm hle fun x hx => ?_
      have : toD x ∈ S'.comap (ofDL (D := D)) := by rw [h1]; exact (mem_cjV x).1 hx
      exact this
  · intro h
    apply hw0
    apply ofD_injective
    rw [h]; rfl
  · intro a
    rw [Edd_ofD, hwa, smul_smul, sg_sq, smul_ofD, lowK_rev]
    congr 1
    push_cast
    simp
  · intro a b hab hε
    rw [Edd_ofD, hwb _ _ (Fin.rev_lt_rev.mpr hab) hε.symm, smul_zero]
    rfl

theorem casimir_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (u : D) :
    casimir (Edd ε E) (ofD u) = ofD (casimir E u) := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Edd_ofD, ofD_sum, LinearMap.map_smul, smul_smul]
  conv_lhs => rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev]
  have h1 : -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) * -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) = 1 := by
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem le_genSub' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genSub E S := le_sInf fun _ hT => hT.1

theorem genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem genSub_le' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {S T : Submodule ℂ M} (hS : S ≤ T) (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T :=
  sInf_le ⟨hS, hT⟩

theorem mem_genSub_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) {u : D}
    (hu : u ∈ genSub E V) : ofD u ∈ genSub (Edd ε E) (cjV V) := by
  have hle : genSub E V ≤ (genSub (Edd ε E) (cjV V)).comap (ofDL (D := D)) := by
    refine genSub_le' E (fun v hv => (le_genSub' (Edd ε E) (cjV V) ((mem_cjV (ofD v)).2 hv) : ofD v ∈ genSub (Edd ε E) (cjV V))) fun a b v hv => ?_
    show ofD (E a b v) ∈ _
    rw [ofD_E ε E a b v]
    exact Submodule.smul_mem _ _ (genSub_stable' (Edd ε E) (cjV V) _ _ (hv : ofD v ∈ genSub (Edd ε E) (cjV V)))
  exact hle hu

def Tf (ε : Fin n → Bool) (f : Fin n → D) : Fin n → cjSub D := fun c => ofD (sg ε c • f (Fin.rev c))

def Tfh (ε : Fin n → Bool) : (Fin n → D) →+ (Fin n → cjSub D) where
  toFun := Tf ε
  map_zero' := by
    funext c
    show ofD (sg ε c • (0 : D)) = 0
    rw [smul_zero]; rfl
  map_add' f g := by
    funext c
    show ofD (sg ε c • (f (Fin.rev c) + g (Fin.rev c))) = ofD (sg ε c • f (Fin.rev c)) + ofD (sg ε c • g (Fin.rev c))
    rw [smul_add, ofD_add]

theorem Tf_smul (ε : Fin n → Bool) (z : ℂ) (f : Fin n → D) : Tfh ε (z • f) = conj z • Tfh ε f := by
  funext c
  show ofD (sg ε c • (z • f (Fin.rev c))) = conj z • ofD (sg ε c • f (Fin.rev c))
  rw [smul_ofD, Complex.conj_conj, smul_comm]

theorem Tf_inj (ε : Fin n → Bool) {g : Fin n → D} (h : Tf ε g = 0) : g = 0 := by
  funext c
  have h1 := congrFun h (Fin.rev c)
  simp only [Tf, Fin.rev_rev, Pi.zero_apply] at h1
  have h2 : sg ε (Fin.rev c) • g c = 0 := ofD_injective (h1.trans ofD_zero.symm)
  exact (smul_eq_zero.mp h2).resolve_left (sg_ne ε _)

theorem weightVector_tensor_eq_dual (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    eeV (Edd ε E) (Tf ε f) = Tf ε (eeVd E f) := by
  funext d
  simp only [Tf, eeV, eeVd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, prj, LinearMap.proj_apply, Edd_ofD, LinearMap.map_smul, smul_smul]
  rw [← ofD_sum]
  congr 1
  rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← neg_smul]
  congr 1
  linear_combination (-sg ε d) * sg_sq ε c

theorem prodShift_eq {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = ((List.ofFn θ).map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod := by
  unfold prodShift; rw [List.map_ofFn]; rfl

theorem prodShift_aeval {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = Polynomial.aeval A (∏ t, (Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  unfold prodShift
  congr 2
  funext t
  simp [Algebra.algebraMap_eq_smul_one]

theorem prodShift_rev {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A (fun t => θ (Fin.rev t)) = prodShift A θ := by
  rw [prodShift_aeval, prodShift_aeval]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun t => Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))

theorem list_inter {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →+ Y) (hs : ∀ (z : ℂ) (x : X), T (z • x) = conj z • T x) (A : Module.End ℂ Y)
    (B : Module.End ℂ X) (hAB : ∀ x, T (B x) = A (T x)) (L : List ℝ) (x : X) :
    T ((L.map fun r : ℝ => B - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod x) =
      (L.map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ Y)).prod (T x) := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [map_sub, hAB, hs, Complex.conj_ofReal, ih]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

