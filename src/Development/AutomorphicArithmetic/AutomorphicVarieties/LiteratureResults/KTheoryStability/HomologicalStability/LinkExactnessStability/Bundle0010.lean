import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtOfLinksOutsideExactAtOfConed
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem exactAt_of_links_cone : ∀ (V : Type) (F : Set (List V)) (S : Set V) (y : V), SubClosed F →
    (∀ l ∈ linkIn F S [], y :: l ∈ F) → ∀ (p : ℕ),
    (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
      ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S y hF hy p hlink c hc hbd
  obtain ⟨b, hb, hc', hbd'⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p hlink c hc hbd
  obtain ⟨b', hb', hbb'⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone V F (linkIn F S []) y hy p (c - bd V b) hc' hbd'
  refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
  rw [map_add, hbb']
  abel

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsBdOfCycleFormsKillUnimodularVector
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

theorem cycle_formsKill_bound_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  intro R _ s hs n hlow p u hu hpn c hc hcz
  obtain ⟨f, hf⟩ := hu
  obtain ⟨w, hwu⟩ : ∃ w : Fin n → R, w ⬝ᵥ u = 1 := ⟨_, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  obtain ⟨hsc, -, hchar, -⟩ := GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R n
  have hγF : [(u, w)] ∈ splitSeq R n := by
    rw [hchar]
    simp [hwu]
  have hGeq : {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} =
      {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    ext σ
    simp
  rw [hGeq] at hc
  have hG'sc : SubClosed {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0} := by
    intro l hl l' hl'
    exact ⟨hsc l hl.1 l' hl', fun y hy => hl.2 y (hl'.subset hy)⟩
  have hlinks : ∀ τ ∈ {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0},
      ∀ (x : (Fin n → R) × (Fin n → R)), τ.getLast? = some x →
        x ∉ {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} → τ.length ≤ p →
        ExactAt (linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
          {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} τ) (p - τ.length) := by
    intro τ hτ x hlast hxS hlen
    obtain ⟨ρ, hρ, hρlen, hlink⟩ := GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn R n _ τ hγF hτ.1 hτ.2
    rw [hlink]
    have ht : 1 ≤ τ.length := by
      cases τ with
      | nil => simp at hlast
      | cons a t => simp
    simp only [List.length_singleton] at hρlen
    refine GlobalTheory.T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq R s hs n (n - ρ.length) (p - τ.length) ρ hρ ?_ ?_ ?_
    · omega
    · omega
    · apply hlow
      · omega
      · omega
  obtain ⟨b1, hb1, hc1, hz1⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links _ _ _ hG'sc p hlinks c hc hcz
  have hcone : ∀ l ∈ linkIn {x | x ∈ splitSeq R n ∧ ∀ y ∈ x, ∀ z ∈ [(u, w)], y.2 ⬝ᵥ z.1 = 0}
      {y : (Fin n → R) × (Fin n → R) | ∀ z ∈ [(u, w)], z.2 ⬝ᵥ y.1 = 0} [],
      (u, w) :: l ∈ splitSeq R n := by
    intro l hl
    obtain ⟨hlS, hlG⟩ := hl
    simp only [List.nil_append] at hlG
    obtain ⟨hlF, hlo⟩ := hlG
    rw [hchar] at hlF ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hwu
      · exact hlF.1 y hy
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ⟨?_, ?_⟩, hlF.2⟩
      · simpa using hlS z hz
      · simpa using hlo z hz
  obtain ⟨b2, hb2, hbd2⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone _ (splitSeq R n) _ (u, w) hcone p _ hc1 hz1
  refine ⟨b1 + b2, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ hb2
    refine Finsupp.supported_mono ?_ hb1
    intro l hl
    exact ⟨hl.1.1, hl.2⟩
  · rw [map_add, hbd2]
    abel

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_bd_of_cycle_forms_kill_unimodular_vector : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, (∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') → ∀ (p : ℕ) (u : Fin n → R), [u] ∈ uniSeq R n → 2 * p + s + 1 ≤ n → ∀ c ∈ chains {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} p, bd _ c = 0 → ∃ b ∈ chains (splitSeq R n) (p + 1), bd _ b = c := by
  first
  | exact @GlobalTheory.SeqCx.cycle_formsKill_bound_splitSeq
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.FaceStdSeqGLConjugateCommutingStab
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

noncomputable section

open scoped Matrix

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

def pm (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) R := Matrix.of fun a b => if f b = a then 1 else 0

theorem pm_mul (f h : Fin n → Fin n) : pm R f * pm R h = pm R (f ∘ h) := by
  ext a c
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

theorem pm_id : pm R (id : Fin n → Fin n) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [pm]
  · simp [pm, Matrix.one_apply, h, Ne.symm h]

def pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) : GL (Fin n) R :=
  ⟨pm R f, pm R g, by rw [pm_mul, show f ∘ g = id from funext h1, pm_id],
    by rw [pm_mul, show g ∘ f = id from funext h2, pm_id]⟩

theorem pm_mulVec (f : Fin n → Fin n) (k : Fin n) :
    pm R f *ᵥ (fun a : Fin n => if a = k then (1 : R) else 0) = fun a => if a = f k then 1 else 0 := by
  funext a
  simp only [pm, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : a = f k
  · simp [h]
  · simp [h, Ne.symm h]

theorem vecMul_pm (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (k : Fin n) :
    (fun a : Fin n => if a = k then (1 : R) else 0) ᵥ* pm R g = fun c => if c = f k then 1 else 0 := by
  funext c
  have key : g c = k ↔ c = f k := ⟨fun e => by rw [← e, h1], fun e => by rw [e, h2]⟩
  simp only [pm, Matrix.vecMul, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [key]

theorem pm_mul_apply (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k)
    (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) : (pm R f * M) a c = M (g a) c := by
  have key : ∀ b, f b = a ↔ b = g a := fun b => ⟨fun e => by rw [← e, h2], fun e => by rw [e, h1]⟩
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_pm_apply (f : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) R) (a c : Fin n) :
    (M * pm R f) a c = M a (f c) := by
  simp [pm, Matrix.mul_apply, mul_ite, Finset.sum_ite_eq]

variable (m i : ℕ) (hmi : m + i < n)

def cyc (k : Fin n) : Fin n :=
  if h : m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then ⟨k + 1, by omega⟩
  else if (k : ℕ) = m + i then ⟨m, by omega⟩ else k

def cycInv (k : Fin n) : Fin n :=
  if h : m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then ⟨k - 1, by omega⟩
  else if (k : ℕ) = m then ⟨m + i, hmi⟩ else k

theorem cyc_val (k : Fin n) : (cyc m i hmi k : ℕ) =
    if m ≤ (k : ℕ) ∧ (k : ℕ) < m + i then (k : ℕ) + 1 else if (k : ℕ) = m + i then m else k := by
  unfold cyc; split_ifs <;> rfl

theorem cycInv_val (k : Fin n) : (cycInv m i hmi k : ℕ) =
    if m < (k : ℕ) ∧ (k : ℕ) ≤ m + i then (k : ℕ) - 1 else if (k : ℕ) = m then m + i else k := by
  unfold cycInv; split_ifs <;> rfl

theorem cyc_cycInv (k : Fin n) : cyc m i hmi (cycInv m i hmi k) = k := by
  apply Fin.ext
  rw [cyc_val, cycInv_val]
  split_ifs <;> omega

theorem cycInv_cyc (k : Fin n) : cycInv m i hmi (cyc m i hmi k) = k := by
  apply Fin.ext
  rw [cycInv_val, cyc_val]
  split_ifs <;> omega

end GlobalTheory.HomStab.FacePerm

namespace GlobalTheory.HomStab.FacePerm

variable (R : Type) [CommRing R] {n : ℕ}

theorem pairAct_pmU (f g : Fin n → Fin n) (h1 : ∀ k, f (g k) = k) (h2 : ∀ k, g (f k) = k) (K : ℕ)
    (hK : K < n) (L : ℕ) (hL : (f ⟨K, hK⟩ : ℕ) = L) :
    pairAct R n (pmU R f g h1 h2) ((fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0)) =
    ((fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0),
      (fun a : Fin n => if (a : ℕ) = L then (1 : R) else 0)) := by
  subst hL
  have e1 : (fun a : Fin n => if (a : ℕ) = K then (1 : R) else 0) = fun a => if a = ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  have e2 : (fun a : Fin n => if (a : ℕ) = (f ⟨K, hK⟩ : ℕ) then (1 : R) else 0) = fun a => if a = f ⟨K, hK⟩ then 1 else 0 := by
    funext a
    simp [Fin.ext_iff]
  rw [e1, e2]
  exact Prod.ext (pm_mulVec R f ⟨K, hK⟩) (vecMul_pm R f g h1 h2 ⟨K, hK⟩)

end GlobalTheory.HomStab.FacePerm

open GlobalTheory.HomStab.FacePerm in

theorem GlobalTheory.HomStab.exists_perm_face_stdSeq : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  intro R _ n p h i
  have hi := i.isLt
  have hmi : n - (p + 1) + (i : ℕ) < n := by omega
  refine ⟨pmU R (cyc (n - (p + 1)) i hmi) (cycInv (n - (p + 1)) i hmi) (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), ?_, ?_⟩
  · apply Subtype.ext
    show ((stdList R n (p + 1)).eraseIdx i).map (pairAct R n _) = stdList R n p
    apply List.ext_getElem
    · simp only [List.length_map, List.length_eraseIdx, stdList, List.length_ofFn]
      split_ifs <;> omega
    · intro j h1 h2
      have hjp : j < p := by simpa [stdList] using h2
      simp only [List.getElem_map, List.getElem_eraseIdx, stdList, List.getElem_ofFn, Fin.val_mk]
      split_ifs with hj
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
      · exact pairAct_pmU R _ _ _ _ _ (by omega) _ (by simp only [cyc_val, Fin.val_mk]; split_ifs <;> omega)
  · intro x
    have lo1 : ∀ k : Fin n, ((cyc (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cyc_val]
      split_ifs <;> omega
    have lo2 : ∀ k : Fin n, ((cycInv (n - (p + 1)) i hmi k : ℕ) < n - (p + 1) ↔ (k : ℕ) < n - (p + 1)) := by
      intro k
      rw [cycInv_val]
      split_ifs <;> omega
    have fx1 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cyc (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cyc_val]
      split_ifs <;> omega
    have fx2 : ∀ k : Fin n, (k : ℕ) < n - (p + 1) → cycInv (n - (p + 1)) i hmi k = k := by
      intro k hk
      apply Fin.ext
      rw [cycInv_val]
      split_ifs <;> omega
    have bij : ∀ a c : Fin n, cycInv (n - (p + 1)) i hmi a = c ↔ a = cyc (n - (p + 1)) i hmi c := by
      intro a c
      constructor
      · rintro rfl
        rw [cyc_cycInv]
      · rintro rfl
        rw [cycInv_cyc]
    ext a c
    rw [Units.val_mul, Units.val_mul]
    show ((pm R (cyc (n - (p + 1)) i hmi) * padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) : Matrix (Fin n) (Fin n) R)) a c = ((padMat R (x : Matrix (Fin (n - (p + 1))) (Fin (n - (p + 1))) R) * pm R (cyc (n - (p + 1)) i hmi) : Matrix (Fin n) (Fin n) R)) a c
    rw [pm_mul_apply R _ _ (cyc_cycInv _ _ hmi) (cycInv_cyc _ _ hmi), mul_pm_apply]
    by_cases ha : (a : ℕ) < n - (p + 1)
    · by_cases hc : (c : ℕ) < n - (p + 1)
      · rw [fx2 a ha, fx1 c hc]
      · simp only [padMat, Matrix.of_apply]
        rw [dif_neg, dif_neg]
        all_goals first
          | simp only [bij]
          | (rw [lo1]; omega)
          | (rw [lo2]; omega)
    · simp only [padMat, Matrix.of_apply]
      rw [dif_neg, dif_neg]
      all_goals first
        | simp only [bij]
        | (rw [lo1]; omega)
        | (rw [lo2]; omega)

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab : ∀ (R : Type) [CommRing R] (n p : ℕ) (h : p + 1 ≤ n) (i : Fin (p + 1)), ∃ g : GL (Fin n) R, g • face R n p i (stdSeq R n (p + 1) h) = stdSeq R n p (by omega) ∧ ∀ x : GL (Fin (n - (p + 1))) R, g * stab R (n - (p + 1)) n (Nat.sub_le _ _) x = stab R (n - (p + 1)) n (Nat.sub_le _ _) x * g := by
  first
  | exact @GlobalTheory.HomStab.exists_perm_face_stdSeq
  | exact @GlobalTheory.HomStab.FacePerm.pairAct_pmU
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_cyc
  | exact @GlobalTheory.HomStab.FacePerm.cyc_cycInv
  | exact @GlobalTheory.HomStab.FacePerm.cycInv_val
  | exact @GlobalTheory.HomStab.FacePerm.cyc_val
  | exact @GlobalTheory.HomStab.FacePerm.mul_pm_apply
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul_apply
  | exact @GlobalTheory.HomStab.FacePerm.vecMul_pm
  | exact @GlobalTheory.HomStab.FacePerm.pm_mulVec
  | exact @GlobalTheory.HomStab.FacePerm.pm_id
  | exact @GlobalTheory.HomStab.FacePerm.pm_mul
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PtHCompPermMapOfEquivariant
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem ptH_comp_permMap_eq : ∀ (k G H H' X Y : Type) [CommRing k] [Group G] [Group H] [Group H'] [MulAction G X] [MulAction G Y] (φ : H →* G) (φ' : H' →* G) (σ : H' →* H) (x : X) (hx : ∀ h, φ' h • x = x) (y : Y) (hy : ∀ h, φ h • y = y) (f : X → Y) (hf : ∀ (g : G) z, f (g • z) = g • f z) (g : G), φ.comp σ = φ' → g • f x = y → (∀ h, g * φ' h = φ' h * g) → ∀ n : ℕ, ptH k φ' x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n = groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ (𝟙 (Rep.trivial k H' k)) n ≫ ptH k φ y hy n := by
  intro k G H H' X Y _ _ _ _ _ _ φ φ' σ x hx y hy f hf g hσ hgy hc n
  subst hσ
  have hfx : ∀ h, (φ.comp σ) h • f x = f x := fun h => by rw [← hf, hx]
  have hy' : ∀ h, (φ.comp σ) h • y = y := fun h => hy (σ h)
  have h1 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := perm k G X) (C := perm k G Y)
    (φ.comp σ) (MonoidHom.id G) (ptMap (φ.comp σ) x hx (Rep.trivial k G k))
    (permMap f hf (Rep.trivial k G k)) n
  have hmor : (ptMap (φ.comp σ) x hx (Rep.trivial k G k) ≫
      (Rep.resFunctor (φ.comp σ)).map (permMap f hf (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm k G Y)) =
      ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k) := by
    ext a
    change (Finsupp.mapDomain f (Finsupp.single x (1:k))) a = (Finsupp.single (f x) (1:k)) a
    rw [Finsupp.mapDomain_single]
  have hL : ptH k (φ.comp σ) x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) n :=
    h1.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor)
  have h2 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := Rep.trivial k H k) (C := perm k G Y)
    σ φ (𝟙 (Rep.trivial k H' k)) (ptMap φ y hy (Rep.trivial k G k)) n
  have hmor2 : (𝟙 (Rep.trivial k H' k) ≫ (Rep.resFunctor σ).map (ptMap φ y hy (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm k G Y)) =
      ptMap (φ.comp σ) y hy' (Rep.trivial k G k) := by
    ext a
    rfl
  have hR : groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ
      (𝟙 (Rep.trivial k H' k)) n ≫ ptH k φ y hy n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) n :=
    h2.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor2)
  rw [hL, hR]
  symm
  refine GlobalTheory.HomStab.groupHomology_map_conj k G H' (Rep.trivial k H' k) (perm k G Y) (φ.comp σ) (φ.comp σ)
    (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) g
    (fun h => by rw [hc h, mul_inv_cancel_right]) (fun a => ?_) n
  subst hgy
  change Finsupp.single (g • f x) a = Finsupp.mapDomain (fun z => g • z) (Finsupp.mapRange id rfl (Finsupp.single (f x) a))
  rw [Finsupp.mapRange_id, Finsupp.mapDomain_single]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStabilisationInjectiveBottom
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem injective_stabilisation_bottom_of_rows_exact : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  intro k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur
  have hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
    refine T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_
    intro p q hp hpq
    refine T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev hp hpq
    · intro hodd
      have h3 : 3 ≤ p := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)
  have h0 := hcomm 0 i (by omega)
  have h1 := hcomm 1 i (by omega)
  simp only [Even.zero, if_true] at h0
  have h1' : e 2 i ≫ hMap (d 1) i = 0 := by
    simpa using h1
  haveI := hiso 1 i (by omega)
  haveI := hiso 2 i (by omega)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0 := by
    have := congrArg (fun f => f.hom x) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  obtain ⟨y, hy⟩ := (hE _).mp hx1
  have hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]
    rfl
  have hzero : (e 1 i).hom x = 0 := by
    rw [← hy, hy2]
    have := congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    rfl
  have : x = (inv (e 1 i)).hom ((e 1 i).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]
    rfl
  rw [this, hzero, map_zero]

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_injective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  first
  | exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem SeqCx.exactAt_of_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
    (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S hF p h c hc hcb
  have hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q := by
    intro q
    apply Finsupp.supported_mono
    rintro l ⟨⟨_, hl⟩, hlen⟩
    exact ⟨by simpa using hl, hlen⟩
  by_cases h0 : ([] : List V) ∈ F
  · obtain ⟨b, hb, hcb', hcyc⟩ :=
      T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb
    obtain ⟨b', hb', hbd⟩ := h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc
    refine ⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩
    rw [map_add, hbd]
    abel
  · have hFe : ∀ l, l ∉ F := fun l hl => h0 (hF l hl [] (List.nil_sublist l))
    have hc0 : c = 0 := by
      have : {l : List V | l ∈ F ∧ l.length = p} = ∅ := by
        ext l
        simp [hFe l]
      have hc' := hc
      simp only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'
      exact hc'
    exact ⟨0, Submodule.zero_mem _, by simp [hc0]⟩

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqComplex_exactAt_of_all_links_exactAt : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_of_links
end
end

