import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Matrix

namespace GlobalTheory.SignedParTest

theorem isEnum_unique {n : ℕ} {S : SPar} {l l' : Fin n → ℝ} {e e' : Fin n → Bool}
    (h : IsEnum S l e) (h' : IsEnum S l' e') : l = l' ∧ e = e' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ e' b = e a := by
    intro a
    have : (q a, e a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ a, ∃ b, q b = q' a := by
    intro a
    have : (q' a, e' a) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb⟩
  have hr : Set.range l = Set.range l' := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb, -⟩ := key a; exact ⟨b, by rw [hq, hq', hb]⟩
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb⟩ := key' a; exact ⟨b, by rw [hq, hq', hb]⟩
  have hl : l = l' := (ha.range_inj ha').1 hr
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have : l' b = l' a := by rw [hq' b, hb, ← hq a, hl]
  rw [ha'.injective this] at he
  exact he.symm

theorem goodPar_add {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : p + q = n := by
  obtain ⟨l, e, -, -, hp, hq⟩ := h
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => e a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  omega

theorem goodPar_ex : GoodPar 2 1 1 {(1 / 2, true), (-1 / 2, false)} := by
  refine ⟨![1 / 2, -1 / 2], ![true, false], ⟨?_, ![1 / 2, -1 / 2], ?_, ?_⟩, ⟨?_, ?_⟩, by decide, by decide⟩
  · intro a b; fin_cases a <;> fin_cases b <;> simp <;> norm_num
  · intro a; fin_cases a <;> simp
  · ext x; simp [Fin.exists_fin_two, eq_comm]
  · intro a b; fin_cases a <;> fin_cases b <;> simp <;> norm_num
  · intro a; fin_cases a
    · exact ⟨0, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

theorem lamSH_int (R : Ranks) (P : HCParam R) (a : Fin (2 * R.rS + R.k + 1)) :
    ∃ m : ℤ, lamSH R P a - (((2 * R.rS + R.k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨t, ht⟩ := R.k_even
  have : ∃ z : ℤ, lamSH R P a = z := by
    unfold lamSH lamS
    split_ifs with h h'
    · obtain ⟨z, hz⟩ := P.v_int ⟨_, h⟩; exact ⟨z, by rw [hz]; simp⟩
    · obtain ⟨z, hz⟩ := P.b_int ⟨_, h'⟩; exact ⟨-z, by rw [hz]; simp⟩
    · exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := this
  refine ⟨z - R.rS - t, ?_⟩
  rw [hz, ht]; push_cast; ring

theorem isoDef_wrong_sign {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Matrix (Fin 1) (Fin 1) ℂ → Module.End ℂ M) (x : ℚ) : isoDef 1 π {(x, false)} = ⊥ := by
  unfold isoDef
  rw [sSup_eq_bot]
  rintro W ⟨H, _, _, σ, lam, ε, P, T, ⟨-, q, -, hS⟩, -, -, hP, -⟩
  exfalso
  have he : ε 0 = false := by
    have : (q 0, ε 0) ∈ ({(x, false)} : SPar) := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    exact congrArg Prod.snd (Finset.mem_singleton.1 this)
  have := congrArg Complex.re (congrFun (congrFun hP 0) 0)
  simp [Matrix.mul_apply, Formalism.REAL.Jm, he] at this
  nlinarith [mul_self_nonneg (P 0 0).re, mul_self_nonneg (P 0 0).im]

theorem rho2C_two_one : rhoOfIndex (p := 2) (q := 1) (.inl 0) = 1 ∧ rhoOfIndex (p := 2) (q := 1) (.inl 1) = -1 ∧
    rhoOfIndex (p := 2) (q := 1) (.inr 0) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [rhoOfIndex, Finset.card_filter, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one] <;>
  simp [posC]

theorem blattner_add_rho2C {p q : ℕ} {lam : Ix p q → ℚ} (h : IsParam lam) (a : Ix p q) :
    blattner lam a + rhoOfIndex a = lam a +
      (((Finset.univ.filter fun b => lam b < lam a).card : ℚ) -
        ((Finset.univ.filter fun b => lam a < lam b).card : ℚ)) / 2 := by
  classical
  have pos : ∀ a b : Ix p q, posC a b ↔ sameBlock a b ∧ lam b < lam a := by
    intro a b
    refine ⟨fun hh => ⟨by cases a <;> cases b <;> simp_all [posC, sameBlock], h.2.1 a b hh⟩, fun ⟨h1, h2⟩ => ?_⟩
    by_contra hn
    rcases a with a | a <;> rcases b with b | b
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inl b) (.inl a) e)
      · subst e; exact lt_irrefl _ h2
    · exact h1
    · exact h1
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inr b) (.inr a) e)
      · subst e; exact lt_irrefl _ h2
  have sym : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  simp only [blattner, rhoNC, rhoOfIndex, Finset.card_filter, pos, sym _ a]
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.sum_div, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : sameBlock a b <;> by_cases h2 : lam b < lam a <;> by_cases h3 : lam a < lam b <;>
    simp [h1, h2, h3] <;> norm_num

theorem blattner_inj {p q : ℕ} {l l' : Ix p q → ℚ} (h : IsParam l) (h' : IsParam l') (e : blattner l = blattner l') :
    l = l' := by
  classical
  have mono : ∀ {m : Ix p q → ℚ}, IsParam m → ∀ a b, m b < m a → blattner m b + rhoOfIndex b < blattner m a + rhoOfIndex a := by
    intro m hm a b hab
    rw [blattner_add_rho2C hm, blattner_add_rho2C hm]
    have h1 : ((Finset.univ.filter fun c => m c < m b).card : ℚ) ≤ (Finset.univ.filter fun c => m c < m a).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    have h2 : ((Finset.univ.filter fun c => m a < m c).card : ℚ) ≤ (Finset.univ.filter fun c => m b < m c).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    linarith
  have one : ∀ {m m' : Ix p q → ℚ}, IsParam m → IsParam m' → blattner m = blattner m' →
      ∀ a b, m b < m a → m' b < m' a := by
    intro m m' hm hm' e a b hab
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with x | x
    · have := mono hm a b hab
      have := mono hm' b a x
      rw [e] at *; linarith
    · rw [hm'.1 x] at hab; exact lt_irrefl _ hab
  have ord : ∀ a b, l b < l a ↔ l' b < l' a := fun a b => ⟨one h h' e a b, one h' h e.symm a b⟩
  funext a
  have x := blattner_add_rho2C h a
  have y := blattner_add_rho2C h' a
  simp only [ord] at x
  rw [e] at x
  linarith

def rhoTwo : Ix 2 0 → ℚ := Sum.elim ![1 / 2, -1 / 2] Fin.elim0

theorem blattner_sing : blattner (fun _ : Ix 2 0 => (0 : ℚ)) = blattner rhoTwo := by
  funext a
  rcases a with a | a
  · fin_cases a <;>
    simp only [blattner, rhoNC, Finset.card_filter, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_zero] <;>
    simp [rhoTwo, sameBlock] <;> norm_num
  · exact a.elim0

theorem hasParam_sing {T : GrpData 2 0} (R : DSRep T) : HasParam R (fun _ => 0) ↔ HasParam R rhoTwo := by
  unfold HasParam; rw [blattner_sing]

theorem hasParam_zero {T : GrpData 0 0} (R : DSRep T) (lam : Ix 0 0 → ℚ) : HasParam R lam := by
  refine ⟨?_, fun μ v _ => by simp [vogan]⟩
  haveI := R.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.U.H)
  have hfin : Finite T.G := by
    have hinj : Function.Injective fun g : T.G => ((T.sq g : ℂˣ) : ℂ) := by
      intro g h e
      refine T.emb.injective (Prod.ext (Units.ext (Subsingleton.elim _ _)) (Units.ext e))
    have hsub : Set.range (fun g : T.G => ((T.sq g : ℂˣ) : ℂ)) ⊆ {1, -1} := by
      rintro _ ⟨g, rfl⟩
      have := T.sq_sq g
      rw [Matrix.det_isEmpty] at this
      simpa using this
    have := (Set.toFinite _).subset hsub
    exact Set.finite_univ_iff.1 (Set.Finite.of_finite_image (by rwa [Set.image_univ]) hinj.injOn)
  obtain ⟨v, hv⟩ := (R.ι_range x).2 (by
    unfold KFin
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _))
  refine ⟨v, fun h => hx (by rw [← hv, h, map_zero]), ?_⟩
  simp [hwSub, wtSub]

end GlobalTheory.SignedParTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotHasInfExpThird
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isVolMeasG_const (D : D7) (W : HSp D) (P Q : ℕ) (μ : Measure (GA D W)) :
    IsVolMeasG D W (fun _ => P) (fun _ => Q) μ ↔ IsVolMeas D W P Q μ := Iff.rfl

theorem volTie_of_volTieG (D : D7) (h : VolTieG D) : VolTie D := by
  intro W P Q hW hs
  have h1 := h W hW
  simp only [hs] at h1
  exact h1

theorem gq_smul (D : D7) (W : HSp D) (γ : GQ W) (g : GA D W) : γ • g = (γ : GA D W) * g := rfl

theorem top_AE (D : D7) : (inferInstance : TopologicalSpace (AE D)) = moduleTopology (AF D.host.F) (AE D) := rfl

theorem not_isVolMeasG_zero (D : D7) (W : HSp D) (P Q : D.what₂.Tau → ℕ) : ¬ IsVolMeasG D W P Q 0 := by
  intro h
  have := h.1
  have h2 := (isOpen_univ (X := GA D W)).measure_ne_zero (0 : Measure (GA D W)) ⟨1, trivial⟩
  simp at h2

theorem congr_of_isVolMeasG (D : D7) (W : HSp D) (P Q : D.what₂.Tau → ℕ) (μ : Measure (GA D W))
    (h : IsVolMeasG D W P Q μ) (ρ : D.what₂.Tau) :
    ∃ A : Matrix (Fin (P ρ) ⊕ Fin (Q ρ)) (Fin W.rank) ℂ, Aᴴ * Formalism.UG.Jpq (P ρ) (Q ρ) * A = gramAt D W ρ := by
  obtain ⟨-, ⟨θ, hθ⟩, h2⟩ := h
  obtain ⟨⟨A, hA⟩, -⟩ := h2 θ hθ
  exact ⟨A ρ, hA ρ⟩

theorem one_hecke (D : D7) : IsHeckeChar D 1 ∧ UnramEverywhere D 1 :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ => rfl⟩

theorem not_resEta_one (D : D7) : ¬ ResEta D 1 1 := by
  rintro ⟨⟨η, hη⟩, h⟩
  apply hη.2.2.2
  ext1 a
  simpa using (h η hη a).symm

theorem resEta_zero_iff (D : D7) (χ : (AE D)ˣ →* Circle) :
    ResEta D χ 0 ↔ (∃ η, IsEta D η) ∧ ∀ a, χ (idF D a) = 1 := by
  constructor
  · rintro ⟨⟨η, hη⟩, h⟩
    exact ⟨⟨η, hη⟩, fun a => by simpa using h η hη a⟩
  · rintro ⟨h1, h⟩
    exact ⟨h1, fun η _ a => by simpa using h a⟩

theorem not_hasInfExp_third (D : D7) (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) : ¬ HasInfExp D χ τ (1 / 3) := by
  rintro ⟨n, hn, -⟩
  have h3 : (3 * n : ℚ) = 2 := by rw [hn]; norm_num
  have h4 : 3 * n = 2 := by exact_mod_cast h3
  omega

theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

theorem isomEmb_inj (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (h : HSpace.IsIsomEmb V' V ι) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply V'.nondeg.1
  intro y
  rw [← h x y, hx]
  simp

end GlobalTheory.VolHeckeCheck

end
end

