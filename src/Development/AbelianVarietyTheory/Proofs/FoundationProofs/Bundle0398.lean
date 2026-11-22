import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1Gamm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromL
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.UnrCup

theorem ident_c {l : ℕ} [Fact l.Prime] (ar as ars bs bt bst : Fin 2 → Qbar l) (P M N : Matrix (Fin 2) (Fin 2) (Qbar l)) (e : Qbar l)
    (key : om (P *ᵥ as) (M *ᵥ (N *ᵥ bt)) = e * om as (N *ᵥ bt)) :
    (e * om as (N *ᵥ bt) + om ar (M *ᵥ bst)) - (om ars (M *ᵥ (N *ᵥ bt)) + om ar (M *ᵥ bs)) =
      om ar (M *ᵥ (bst - (bs + N *ᵥ bt))) - om (ars - (ar + P *ᵥ as)) (M *ᵥ (N *ᵥ bt)) := by
  simp only [om, Matrix.mulVec_sub, Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

theorem inv_ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (V : R2 Ω l) (H I : Subgroup (G ℚ Ω)) (a : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat V s i j ∈ c.O) → I ≤ H → (∀ s ∈ H, ∀ i ∈ I, s⁻¹ * i * s ∈ I) → Coc1 c n V H a → (∀ i ∈ I, Cv n (a i) 0) → ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) ∧ Cv n (mat V i *ᵥ a s) (a s) := by
  intro l _ Ω _ _ c n V H I a hint hIH hconj ha ha0
  have hVn : ∀ g i j, ‖mat V g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hint g i j)
  have small : ∀ g, ∀ i ∈ I, ∀ j, ‖(mat V g *ᵥ a i) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun g i hi =>
    CupCob.mulVec_le _ _ (hVn g) (fun k => by have := ha0 i hi k; unfold Cg at this; simpa using this)
  have first : ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) := by
    intro s hs i hi j
    have h1 := ha.2.2 s hs i (hIH hi) j
    unfold Cg at h1 ⊢
    have e : a (s * i) j - a s j = (a (s * i) j - (a s + mat V s *ᵥ a i) j) + (mat V s *ᵥ a i) j := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (small s i hi j))
  intro s hs i hi
  refine ⟨first s hs i hi, fun j => ?_⟩
  have hi' : s⁻¹ * i * s ∈ I := hconj s hs i hi
  have e1 : i * s = s * (s⁻¹ * i * s) := by group
  have h1 := ha.2.2 i (hIH hi) s hs j
  have h2 := first s hs _ hi' j
  have h3 := ha0 i hi j
  unfold Cg at h1 h2 h3 ⊢
  rw [e1] at h1
  have e : (mat V i *ᵥ a s) j - a s j = -(a (s * (s⁻¹ * i * s)) j - (a i + mat V i *ᵥ a s) j) - (a i j - (0 : Fin 2 → Qbar l) j) + (a (s * (s⁻¹ * i * s)) j - a s j) := by
    simp only [Pi.add_apply, Pi.zero_apply]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((CupCob.nsub_le_max _ _).trans (max_le (by rw [norm_neg]; exact h1) h3)) h2)

theorem cup_coc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → Coc1 c n W H a → Coc1 c n (dual1 W) H b → ∀ r ∈ H, ∀ s ∈ H, ∀ t ∈ H, Cg n (eps l r * cup W a b s t + cup W a b r (s * t)) (cup W a b (r * s) t + cup W a b r s) := by
  intro l _ Ω _ _ c n W H a b hint hdet ha hb r hr s hs t ht
  have hDm := CupCob.dual_representation_integral c W hdet hint
  have hDn : ∀ g i j, ‖mat (dual1 W) g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hDm g i j)
  have key := CupCob.om_key W hdet r (a s) (mat (dual1 W) s *ᵥ b t)
  unfold Cg
  simp only [cup]
  rw [CupCob.mat_dual1_mul W r s (b t), ident_c (a r) (a s) (a (r * s)) (b s) (b t) (b (s * t)) (mat W r)
    (mat (dual1 W) r) (mat (dual1 W) s) (eps l r) key]
  refine (CupCob.nsub_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (ha.2.1 r i))
      (CupCob.mulVec_le _ _ (hDn r) (fun i => hb.2.2 s hs t ht i))
  · exact CupCob.om_le_left _ _ (fun i => ha.2.2 r hr s hs i) (CupCob.mulVec_le _ _ (hDn r)
      (CupCob.mulVec_le _ _ (hDn s) (fun i => CupCob.norm_le_one_of_mem c (hb.2.1 t i))))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_add {n : ℕ} {a b a' b' : Qbar l} (h : Cg n a b) (h' : Cg n a' b') : Cg n (a + a') (b + b') := by
  unfold Cg at *
  have e : a + a' - (b + b') = (a - b) + (a' - b') := by ring
  rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_sub {n : ℕ} {a b a' b' : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n a' b') : Cv n (a - a') (b - b') := by
  intro i
  unfold Cg at *
  have e : (a - a') i - (b - b') i = (a i - b i) - (a' i - b' i) := by simp only [Pi.sub_apply]; ring
  rw [e]; exact (CupCob.nsub_le_max _ _).trans (max_le (h i) (h' i))

theorem isIntegralCoboundaryTwoModPow_add (c : Coef l) (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ ξ' : G ℚ Ω → G ℚ Ω → Qbar l)
    (h : Cob2 c n H ξ) (h' : Cob2 c n H ξ') : Cob2 c n H (fun s t => ξ s t + ξ' s t) := by
  obtain ⟨u, hu, hui, hu'⟩ := h
  obtain ⟨v, hv, hvi, hv'⟩ := h'
  refine ⟨fun s => u s + v s, hu.add hv, fun s => add_mem (hui s) (hvi s), fun s hs t ht => ?_⟩
  have := cg_add (hu' s hs t ht) (hv' s hs t ht)
  convert this using 1; ring

theorem isIntegralCocycleOneModPow_sub (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a a' : G ℚ Ω → Fin 2 → Qbar l)
    (h : Coc1 c n V H a) (h' : Coc1 c n V H a') : Coc1 c n V H (fun s => a s - a' s) := by
  refine ⟨h.1.sub h'.1, fun s i => sub_mem (h.2.1 s i) (h'.2.1 s i), fun s hs t ht => ?_⟩
  have := cv_sub (h.2.2 s hs t ht) (h'.2.2 s hs t ht)
  intro i
  convert this i using 2
  simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]; ring

theorem isIntegralCocycleOneModPow_coboundary (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : Fin 2 → Qbar l)
    (hV : Continuous fun s => mat V s) (hint : ∀ s i j, mat V s i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) :
    Coc1 c n V H (fun s => mat V s *ᵥ x - x) := by
  refine ⟨(hV.matrix_mulVec continuous_const).sub continuous_const |>.continuousOn,
    fun s i => sub_mem (CupCob.mulVec_mem c _ _ (hint s) hx i) (hx i), fun s _ t _ i => ?_⟩
  have e : (mat V (s * t) *ᵥ x - x) i = ((mat V s *ᵥ x - x) + mat V s *ᵥ (mat V t *ᵥ x - x)) i := by
    simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]; ring
  unfold Cg; dsimp only; rw [e, sub_self, norm_zero]; exact norm_nonneg _

theorem om_cg (c : Coef l) (n : ℕ) (A A' B B' : Fin 2 → Qbar l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hA : ∀ i, A i ∈ c.O) (hB' : ∀ i, B' i ∈ c.O) (hM : ∀ i j, M i j ∈ c.O)
    (h1 : Cv n A' A) (h2 : Cv n B' B) : Cg n (om A' (M *ᵥ B')) (om A (M *ᵥ B)) := by
  have hMn : ∀ i j, ‖M i j‖ ≤ 1 := fun i j => CupCob.norm_le_one_of_mem c (hM i j)
  unfold Cg
  have e : om A' (M *ᵥ B') - om A (M *ᵥ B) = om (A' - A) (M *ᵥ B') + om A (M *ᵥ (B' - B)) := by
    simp only [om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_left _ _ (fun i => h1 i) (CupCob.mulVec_le _ _ hMn (fun i => CupCob.norm_le_one_of_mem c (hB' i)))
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (hA i))
      (CupCob.mulVec_le _ _ hMn (fun i => by simpa [Cg] using h2 i))

theorem mat_dual1_cont (W : R2 Ω l) (hW : Continuous W) (hdet : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
  have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (CupCob.mat_dual1 W hdet)
  rw [this]
  exact (CupCob.eps_cont.mul hM.matrix_det).smul hM

theorem cup_unr_cob_of_vanish [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω)
    (a b : G ℚ Ω → Fin 2 → Qbar l) (hW : Continuous W) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1)
    (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    (ha : Coc1 c n W (Dec (F := ℚ) B) a) (hb : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b)
    (ha0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (a i) 0) (hb0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (b i) 0) :
    Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  set D := Dec (F := ℚ) B with hD
  set I := Ine (F := ℚ) B with hI
  have hID : I ≤ D := Ine_le_Dec B
  have hconj : ∀ s ∈ D, ∀ i ∈ I, s⁻¹ * i * s ∈ I := fun s hs i hi => by
    have := conj_mem_Ine (D.inv_mem hs) hi
    simpa using this
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hia := inv_ine l Ω c n W D I a hint hID hconj ha ha0
  have hib := inv_ine l Ω c n (dual1 W) D I b hDm hID hconj hb hb0
  have hξint : ∀ s t, cup W a b s t ∈ c.O := fun s t =>
    CupCob.om_mem c _ _ (ha.2.1 s) (CupCob.mulVec_mem c _ _ (hDm s) (hb.2.1 t))
  have hepsI : ∀ i ∈ I, eps l i = 1 := fun i hi => by
    have h := cyc_eq_one_of_mem_Ine (F := ℚ) (l := l) hl hB hi
    show ((cycBar ℚ Ω l i : (Qbar l)ˣ) : Qbar l) = 1
    rw [show cycBar ℚ Ω l i = cyc ℚ Ω l i from rfl, h]; rfl
  have hbiI : ∀ s ∈ D, ∀ t ∈ D, ∀ i ∈ I, Cg n (cup W a b (s * i) t) (cup W a b s t) ∧
      Cg n (cup W a b s (t * i)) (cup W a b s t) := by
    intro s hs t ht i hi
    constructor
    · simp only [cup]
      rw [CupCob.mat_dual1_mul W s i (b t)]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (fun j => CupCob.mulVec_mem c _ _ (hDm i) (hb.2.1 t) j) (hDm s)
        (hia s hs i hi).1 (hib t ht i hi).2
    · simp only [cup]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (hb.2.1 _) (hDm s) (fun j => by simp [Cg]) (hib t ht i hi).1
  have hcont : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := by
    have h1 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => a p.1) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      ha.1.comp continuousOn_fst (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => b p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      hb.1.comp continuousOn_snd (fun p hp => hp.2)
    have hm : ∀ i j, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      fun i j => (((continuous_apply j).comp (continuous_apply i)).comp ((mat_dual1_cont W hW hdet).comp continuous_fst)).continuousOn
    have h1' := continuousOn_pi.1 h1
    have h2' := continuousOn_pi.1 h2
    have h3' : ∀ i, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i 0 * b p.2 0 + mat (dual1 W) p.1 i 1 * b p.2 1)
        ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := fun i => ((hm i 0).mul (h2' 0)).add ((hm i 1).mul (h2' 1))
    have e : (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) = fun p => a p.1 0 * (mat (dual1 W) p.1 1 0 * b p.2 0 + mat (dual1 W) p.1 1 1 * b p.2 1) - a p.1 1 * (mat (dual1 W) p.1 0 0 * b p.2 0 + mat (dual1 W) p.1 0 1 * b p.2 1) := by
      funext p; simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e]
    exact ((h1' 0).mul (h3' 1)).sub ((h1' 1).mul (h3' 0))
  obtain ⟨K, hIK, hKD, hKo, hepsK, hbiK⟩ := GlobalTheory.T.open_subgroup_cochain_invariance l Ω n D I (cup W a b) (isClosed_Dec B) hID hcont hepsI hbiI
  obtain ⟨φ, m, hm, hφm, hd⟩ := GlobalTheory.T.exists_frobenius_pow_inv_mul_mem_open_subgroup Ω q B K hB hIK hKo
  obtain ⟨d, hdo, hdK⟩ := hd (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
  exact GlobalTheory.T.cob2_of_cocycle_cong_of_invariant l Ω c n D K φ m d (cup W a b) hm hφm hdo hdK hepsK hξint
    (cup_coc l Ω c n W D a b hint hdet ha hb) hbiK

theorem cup_unr_cob : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → Coc1 c n W (Dec (F := ℚ) B) a → Coc1 c n (dual1 W) (Dec (F := ℚ) B) b → Cob1 c n W (Ine (F := ℚ) B) a → Cob1 c n (dual1 W) (Ine (F := ℚ) B) b → Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  intro _ l _ Ω _ _ _ c n W q B a b hW hint hdet hB hl ha hb ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hMc : Continuous fun s => mat W s := Units.continuous_val.comp hW
  set a0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat W s *ᵥ x - x with ha0def
  set b0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat (dual1 W) s *ᵥ y - y with hb0def
  have ha0 : Coc1 c n W (Dec (F := ℚ) B) a0 := isIntegralCocycleOneModPow_coboundary c n W _ x hMc hint hx
  have hb0 : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b0 := isIntegralCocycleOneModPow_coboundary c n (dual1 W) _ y (mat_dual1_cont W hW hdet) hDm hy
  have ha1 := isIntegralCocycleOneModPow_sub c n W _ a a0 ha ha0
  have hb1 := isIntegralCocycleOneModPow_sub c n (dual1 W) _ b b0 hb hb0
  have hsplit : cup W a b = fun s t => (cup W a0 b s t + cup W (fun s => a s - a0 s) b0 s t) +
      cup W (fun s => a s - a0 s) (fun s => b s - b0 s) s t := by
    funext s t; simp only [cup, om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  have triv : ∀ (V : R2 Ω l) (z : Fin 2 → Qbar l), (∀ i, z i ∈ c.O) → Cob1 c n V (Dec (F := ℚ) B) (fun s => mat V s *ᵥ z - z) :=
    fun V z hz => ⟨z, hz, fun s _ i => by unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _⟩
  have c1 := CupCob.cup_cob l Ω c n W _ a0 b hW hint hdet ha0 hb (Or.inl (triv W x hx))
  have c2 := CupCob.cup_cob l Ω c n W _ _ b0 hW hint hdet ha1 hb0 (Or.inr (triv (dual1 W) y hy))
  have c3 := cup_unr_cob_of_vanish c n W q B _ _ hW hint hdet hB hl ha1 hb1
    (fun i hi j => by
      have := hax i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
    (fun i hi j => by
      have := hby i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
  rw [hsplit]
  exact isIntegralCoboundaryTwoModPow_add c n _ _ _ (isIntegralCoboundaryTwoModPow_add c n _ _ _ c1 c2) c3

end GlobalTheory.Ord2.UnrCup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.OrdCob

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem matQ_one_zero (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) :
    matQ c n W hint s 1 0 = 0 := by
  have h : (⟨mat W s 1 0, hint s 1 0⟩ : c.O) = 0 := Subtype.ext (hB s s.2)
  rw [matQ_apply, h, map_zero]

def rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    Representation (ZMod (l ^ n)) (Dec (F := ℚ) B) (Qn c n) where
  toFun s := (AddMonoidHom.mulLeft (matQ c n W hint s 0 0)).toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint 1 0 0 * x = x
    rw [matQ_one, Matrix.one_apply_eq, one_mul]
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint ((s : G ℚ Ω) * (t : G ℚ Ω)) 0 0 * x =
      matQ c n W hint s 0 0 * (matQ c n W hint t 0 0 * x)
    rw [matQ_mul, Matrix.mul_apply, Fin.sum_univ_two, matQ_one_zero c n W hint B hB t, mul_zero, add_zero,
      mul_assoc]

theorem contAction_rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (hcont : Continuous W) :
    ReciprocityTheory.Gal.ContAction (rhoL c n W hint B hB) := by
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro x
  show Continuous fun s : Dec (F := ℚ) B => matQ c n W hint s 0 0 * x
  exact ((continuous_matQ_apply c n W hint hcont 0 0).comp continuous_subtype_val).mul continuous_const

theorem rhoS_single (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) (u : Qn c n) :
    rhoS c n W hint S hN (locHom (S : Set Pl) B s) (Pi.single 0 u) =
      Pi.single 0 (rhoL c n W hint B hB s u) := by
  show matQ c n W hint s *ᵥ Pi.single 0 u = Pi.single 0 (matQ c n W hint s 0 0 * u)
  have h := matQ_one_zero c n W hint B hB s
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem dual_cob_on_line : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  intro hL l _ Ω _ _ _ c n hn W hint hcont S hN μ hμ B v hBv hB f hf
  have hμχ : ∀ s : Dec (F := ℚ) B,
      μ (locHom (S : Set Pl) B s) = ((cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype) s := fun s =>
    DFunLike.congr_fun hμ (s : G ℚ Ω)
  have hinj := (hL.lt ℚ Ω l n (Qn c n) B (rhoL c n W hint B hB) v hn hBv
    (contAction_rhoL c n W hint B hB hcont)).2.2.1.1
  set χ : Dec (F := ℚ) B →* (ZMod (l ^ n))ˣ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype with hχ
  have hs := rhoS_single c n W hint S hN B hB
  have hs' : ∀ (s : Dec (F := ℚ) B) (u : Qn c n),
      rhoS c n W hint S hN (locHom (S : Set Pl) B s)⁻¹ (Pi.single 0 u) =
        Pi.single 0 (rhoL c n W hint B hB s⁻¹ u) := fun s u => by rw [← map_inv, hs]
  let ι : Qn c n →ₗ[ZMod (l ^ n)] Mn c n := LinearMap.single (ZMod (l ^ n)) (fun _ : Fin 2 => Qn c n) 0
  let r : TDual (ZMod (l ^ n)) (Mn c n) → TDual (ZMod (l ^ n)) (Qn c n) := fun φ =>
    TDual.mk (LinearMap.comp (show Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from φ) ι)
  have hψ : (fun s => r (f.1 s)) ∈ Z1 ((twDual χ (rhoL c n W hint B hB)).comp (MonoidHom.id _)) := by
    refine ⟨(continuous_of_discreteTopology (f := r)).comp f.2.1, fun g h => ?_⟩
    refine TDual.ext fun u => ?_
    have e : f.1 (g * h) (Pi.single 0 u) = f.1 g (Pi.single 0 u) +
        ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) *
          f.1 h (rhoS c n W hint S hN (locHom (S : Set Pl) B g)⁻¹ (Pi.single 0 u)) := by
      rw [f.2.2 g h]; rfl
    rw [hμχ, hs'] at e
    exact e
  have hcup : cupH1H1TwistedDual χ (rhoL c n W hint B hB) (MonoidHom.id _)
      ((contAction_rhoL c n W hint B hB hcont).comp' continuous_id) (Submodule.mkQ _ ⟨_, hψ⟩) = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a0, rfl⟩ := Submodule.mkQ_surjective _ x
    have ha : (fun s => ι (a0.1 s)) ∈ Z1 ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) := by
      refine ⟨(continuous_of_discreteTopology (f := ι)).comp a0.2.1, fun g h => ?_⟩
      show ι (a0.1 (g * h)) = ι (a0.1 g) +
        rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))
      rw [a0.2.2 g h, map_add, hs]
      rfl
    have hmem : Submodule.mkQ _ (⟨_, ha⟩ : Z1 _) ∈ ordCond c n W hint S hN B := by
      refine Submodule.mem_map.2 ⟨⟨_, ha⟩, (mem_ordZ _).2 ⟨0, fun s => ?_⟩, rfl⟩
      show (Pi.single 0 (a0.1 s) : Mn c n) 1 = _
      simp
    obtain ⟨cc, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (hf _ hmem))
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨cc, hcc, ?_⟩)
    funext p
    obtain ⟨g, h⟩ := p
    have e : ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * cc h - cc (g * h) + cc g =
        f.1 g (rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))) := congrFun hd (g, h)
    rw [hμχ, hs] at e
    exact e
  have h0 := hinj (hcup.trans (map_zero _).symm)
  obtain ⟨m0, hm0⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
  refine ⟨TDual.mk (LinearMap.comp (show Qn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from m0) (LinearMap.proj 0)),
    fun s u => ?_⟩
  have e : f.1 s (Pi.single 0 u) =
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * m0 (rhoL c n W hint B hB s⁻¹ u) - m0 u :=
    congrArg (fun φ : TDual (ZMod (l ^ n)) (Qn c n) => φ u) (hm0 s)
  rw [e, twDual_apply, hμχ, hs']
  rfl

end GlobalTheory.Ord2.OrdCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditionsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_local_conditions : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧ ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  first | exact @GlobalTheory.Ord2.Unbounded.divSel_unbounded | exact GlobalTheory.Ord2.Unbounded.divSel_unbounded | (intros; apply GlobalTheory.Ord2.Unbounded.divSel_unbounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionInvariantRealValuation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem exists_real_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∀ x : Ω, v (s x) = v x) ∧ 0 < v (l : Ω) ∧ v (l : Ω) < 1 := by
  intro l _ Ω _ _ _ A h
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨w, hw, hl⟩ := h
    simpa using (hw ((l : ℕ) : 𝓞 ℚ)).2 hl
  obtain ⟨j, hj⟩ := Formalism.BasicNotions.Examples₂.LB.exists_emb (l := l) A hA
  let v : Valuation Ω ℝ≥0 := (NormedField.valuation (K := PadicAlgCl l)).comap j
  have hv : ∀ x : Ω, v x ≤ 1 ↔ x ∈ A := by
    intro x
    rw [hj]
    exact Iff.rfl
  have he : v.IsEquiv A.valuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [hv, A.valuation_le_one_iff]
  refine ⟨v, hv, fun s hs x => ?_, ?_, ?_⟩
  · exact he.eq_iff.2 (GlobalTheory.Dec_valuation_apply_eq ℚ Ω A s hs x)
  · have : CharZero Ω := j.charZero
    have hl : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact zero_lt_iff.mpr ((v.ne_zero_iff).2 hl)
  · exact he.lt_one_iff_lt_one.2 hA

end GlobalTheory.RecOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

theorem coef_free_pairSurj (l : ℕ) [Fact l.Prime] (c : Coef l) : Module.Free ℤ_[l] c.O := by
  haveI : Module.IsTorsionFree ℤ_[l] c.O := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_
    have h' : a • (x : Qbar l) = 0 := by rw [← Subalgebra.coe_smul, h]; rfl
    rw [Algebra.smul_def, mul_eq_zero] at h'
    rcases h' with h' | h'
    · left
      have := congrArg norm h'
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero] at this
      have h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0 := norm_eq_zero.1 this
      exact PadicInt.coe_eq_zero.1 h2
    · right
      exact Subtype.ext h'
  infer_instance

theorem exists_eq_tbA_mul (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)) :
    ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  classical
  haveI := coef_free_pairSurj l c
  let e := Module.Free.chooseBasis ℤ_[l] c.O
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])
  have hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [f, Module.Basis.constr_basis]
      rw [map_natCast, ZMod.natCast_zmod_val]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨b, hb, -⟩ := tau_spec c f
  refine ⟨red c n b, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := red_surjective c n a
  rw [← hf, hb, ← map_mul, tbA_red, mul_comm]

end GlobalTheory.Ord2.SelPerp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrimeStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (H : Subgroup (G ℚ Ω)), H ≤ Dec (F := ℚ) A → ∀ (m : ℕ) (x : Ω), x ∈ A →
  (∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) → ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  first | exact @GlobalTheory.AxSen.exists_fixed_congr | exact GlobalTheory.AxSen.exists_fixed_congr | (intros; apply GlobalTheory.AxSen.exists_fixed_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficientsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  first | exact @GlobalTheory.PerFix.exists_fixed_near | exact GlobalTheory.PerFix.exists_fixed_near | (intros; apply GlobalTheory.PerFix.exists_fixed_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOneStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1GammStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k →
  ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
  α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
  ∀ (σT : ℕ → SL(2, ℤ)) (σD : (ZMod N)ˣ → SL(2, ℤ)),
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) (σT q)) →
    (∀ d : (ZMod N)ˣ, IsDiam N l (d : ZMod N) (σD d)) →
  ∀ z ∈ Z1 (Lev N l) (k - 2), ∀ n : ℕ,
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      ((TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    ((UlZ (Lev N l) (k - 2) l - α • 1) ^ n) z ∈ B1 (Lev N l) (k - 2) →
    (∀ d : (ZMod N)ˣ, ((DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      (TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) z ∈ B1 (Lev N l) (k - 2)) ∧
    (UlZ (Lev N l) (k - 2) l - α • 1) z ∈ B1 (Lev N l) (k - 2) ∧
    (∀ d : (ZMod N)ˣ, (DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) z ∈ B1 (Lev N l) (k - 2)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | exact GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | (intros; apply GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  first | exact @GlobalTheory.Ord2.SelLower.sel_lower | exact GlobalTheory.Ord2.SelLower.sel_lower | (intros; apply GlobalTheory.Ord2.SelLower.sel_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtensionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_cochain_cocycle_extension : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  first | exact @GlobalTheory.br_tame | exact GlobalTheory.br_tame | (intros; apply GlobalTheory.br_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromLStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  first | exact @GlobalTheory.KA.TameUnr.tame_limit_unram | exact GlobalTheory.KA.TameUnr.tame_limit_unram | (intros; apply GlobalTheory.KA.TameUnr.tame_limit_unram <;> assumption)
end

