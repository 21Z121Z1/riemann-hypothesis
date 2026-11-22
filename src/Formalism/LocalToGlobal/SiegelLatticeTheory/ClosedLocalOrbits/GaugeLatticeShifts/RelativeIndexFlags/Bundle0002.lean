import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.ExistsUpUni
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

def RepM (f : Fin (r + 1) → S.V) (φ : S.V ≃ₗ[E] S.V) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ b, φ (f b) = ∑ c, A c b • f c

variable {f : Fin (r + 1) → S.V}

theorem apply_comb {φ : S.V ≃ₗ[E] S.V} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : RepM f φ A)
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (b : Fin (r + 1)) :
    φ (∑ c, B c b • f c) = ∑ d, (A * B) d b • f d := by
  have h' : ∀ c, φ (f c) = ∑ d, A d c • f d := h
  simp only [map_sum, map_smul, h', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem repM_mul {φ ψ : S.V ≃ₗ[E] S.V} {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hA : RepM f φ A) (hB : RepM f ψ B) : RepM f (φ * ψ) (A * B) := fun b => by
  show φ (ψ (f b)) = _
  rw [hB b]
  exact apply_comb hA B b

theorem sum_one (a : Fin (r + 1)) : ∑ d, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) d a • f d = f a := by
  simp [Matrix.one_apply]

theorem repM_inv {n : S.V ≃ₗ[E] S.V} {N : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : RepM f n N)
    (hN : IsUnit N.det) : RepM f n⁻¹ N⁻¹ := fun b => by
  have key : n (∑ c, N⁻¹ c b • f c) = f b := by
    rw [apply_comb h, Matrix.mul_nonsing_inv N hN, sum_one]
  rw [← key]
  exact n.symm_apply_apply _

theorem exists_upUni {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) :
    ∃ N : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni N ∧ RepM (frame F) n N := by
  obtain ⟨-, h1, h2⟩ := hn
  have hzo : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
    | zero => simp
    | add y w _ _ hy hw => simp [hy, hw]
    | smul a y _ hy => simp [hy]
  have hzmem : F.fl.z ∈ orth S (Xsp F) := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun x hx => hzo x hx
  have col : ∀ b : Fin (r + 1), ∃ v : Fin (r + 1) → E,
      (∀ c, b < c → v c = 0) ∧ v b = 1 ∧ n (frame F b) = ∑ c, v c • frame F c := by
    intro b
    cases b using Fin.lastCases with
    | last =>
      have hm : n F.fl.z - F.fl.z ∈ Submodule.span E (Set.range F.fl.e) := h2 _ hzmem
      obtain ⟨d, hd⟩ : ∃ d : Fin r → E, ∑ i, d i • F.fl.e i = n F.fl.z - F.fl.z := by
        rwa [Submodule.mem_span_range_iff_exists_fun] at hm
      refine ⟨Fin.snoc (α := fun _ => E) d 1, fun c hc => absurd hc (not_lt.2 (Fin.le_last c)), by simp, ?_⟩
      simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, one_smul]
      rw [hd]
      abel
    | cast i =>
      have hi : F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1 + 1}) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := h1 i.1 _ hi
      obtain ⟨l, hl, hle⟩ : ∃ l ∈ Finsupp.supported E E {k : Fin r | k.1 < i.1},
          Finsupp.linearCombination E F.fl.e l = n (F.fl.e i) - F.fl.e i := by
        rw [← Finsupp.mem_span_image_iff_linearCombination]
        exact hm
      rw [Finsupp.mem_supported'] at hl
      have hli : l i = 0 := hl i (by simp)
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun k a => a • F.fl.e k) (fun k => zero_smul E _)] at hle
      refine ⟨Fin.snoc (α := fun _ => E) (fun k => if k = i then 1 else l k) 0, ?_, by simp, ?_⟩
      · intro c hc
        cases c using Fin.lastCases with
        | last => simp
        | cast k =>
          have hik : i < k := Fin.castSucc_lt_castSucc_iff.1 hc
          simp only [Fin.snoc_castSucc, if_neg (ne_of_gt hik)]
          exact hl k (by simp only [Set.mem_setOf_eq, not_lt]; exact Fin.le_iff_val_le_val.1 hik.le)
      · have key : ∀ k, (if k = i then (1 : E) else l k) = l k + if k = i then 1 else 0 := by
          intro k
          split_ifs with h
          · simp [h, hli]
          · simp
        simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, key, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hle]
        abel
  choose v hv0 hv1 hvn using col
  refine ⟨fun c b => v b c, ?_, ?_⟩
  · intro i j
    exact ⟨fun hji => hv0 j i hji, fun hij => by subst hij; exact hv1 i⟩
  · intro b
    exact hvn b

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ}

theorem cond_conj (g s : S.V ≃ₗ[E] S.V) {A₁ B₁ A₂ B₂ : Submodule E S.V}
    (hA : ∀ x, x ∈ A₂ ↔ g.symm x ∈ A₁) (hB : ∀ x, x ∈ B₂ ↔ g.symm x ∈ B₁) :
    (∀ y ∈ B₂, s y - y ∈ A₂) ↔ (∀ x ∈ B₁, g.symm (s (g x)) - x ∈ A₁) := by
  constructor
  · intro h x hx
    have h1 : g x ∈ B₂ := (hB _).2 (by simpa using hx)
    have := (hA _).1 (h _ h1)
    simpa [map_sub] using this
  · intro h y hy
    have h1 := h (g.symm y) ((hB y).1 hy)
    rw [hA]
    simpa [map_sub] using h1

variable {T' : E} {F₁ F₂ : LFlag S r T'} {g : S.V ≃ₗ[E] S.V}

theorem e_of_frame (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (i : Fin r) :
    F₂.fl.e i = g (F₁.fl.e i) := by
  have := hfr (Fin.castSucc i)
  simpa [frame, FlagG.fvec] using this

theorem xflag_eq_map (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (j : ℕ) :
    Xflag F₂ j = (Xflag F₁ j).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = fun i => g (F₁.fl.e i) := funext (e_of_frame hfr)
  show Submodule.span E (F₂.fl.e '' _) = (Submodule.span E (F₁.fl.e '' _)).map _
  rw [Submodule.map_span, Set.image_image, he]
  rfl

theorem xsp_eq_map (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) :
    Xsp F₂ = (Xsp F₁).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = fun i => g (F₁.fl.e i) := funext (e_of_frame hfr)
  show Submodule.span E (Set.range F₂.fl.e) = (Submodule.span E (Set.range F₁.fl.e)).map _
  rw [Submodule.map_span, ← Set.range_comp, he]
  rfl

theorem orth_mem (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (hiso : g ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (y : S.V) : y ∈ orth S (Xsp F₂) ↔ g.symm y ∈ orth S (Xsp F₁) := by
  have hi : ∀ x y, S.hT (g x) (g y) = S.hT x y := hiso
  rw [mem_orth_iff, mem_orth_iff, xsp_eq_map hfr]
  constructor
  · intro h x hx
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hi x (g.symm y)]
    simpa using this
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hi x (g.symm y)] at this
    simpa using this

theorem nlam_conj (hg : IsAutLam S Λ g) (hfr : ∀ a, frame F₂ a = g (frame F₁ a))
    (s : S.V ≃ₗ[E] S.V) : s ∈ NLam Λ F₂ ↔ g⁻¹ * s * g ∈ NLam Λ F₁ := by
  have hA : ∀ j x, x ∈ Xflag F₂ j ↔ g.symm x ∈ Xflag F₁ j := fun j x => by
    rw [xflag_eq_map hfr]
    exact Submodule.mem_map_equiv _
  have hX : ∀ x, x ∈ Xsp F₂ ↔ g.symm x ∈ Xsp F₁ := fun x => by
    rw [xsp_eq_map hfr]
    exact Submodule.mem_map_equiv _
  have hO : ∀ x, x ∈ orth S (Xsp F₂) ↔ g.symm x ∈ orth S (Xsp F₁) := orth_mem hfr hg.1
  have hAut : IsAutLam S Λ s ↔ IsAutLam S Λ (g⁻¹ * s * g) := by
    constructor
    · intro h
      exact isAutLam_mul Λ (isAutLam_mul Λ (isAutLam_inv Λ hg) h) hg
    · intro h
      have := isAutLam_mul Λ (isAutLam_mul Λ hg h) (isAutLam_inv Λ hg)
      simpa [mul_assoc] using this
  show (IsAutLam S Λ s ∧ _ ∧ _) ↔ (IsAutLam S Λ (g⁻¹ * s * g) ∧ _ ∧ _)
  rw [hAut]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · exact forall_congr' fun j => cond_conj g s (hA j) (hA (j + 1))
  · exact cond_conj g s hX hO

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

