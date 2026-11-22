import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingLinkFamilyNormalised
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0004
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrSep

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.ColAddGenCastSuccRename
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree

def colEmb (r n : ℕ) : Fin r × Fin n → Fin r × Fin (n + 1) := fun v => (v.1, v.2.castSucc)

theorem rowGen_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen R a b (rename (colEmb r n) f) =
      Polynomial.map ((rename (colEmb r n) : MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin (n + 1)) R) :
        MvPolynomial (Fin r × Fin n) R →+* MvPolynomial (Fin r × Fin (n + 1)) R) (rowGen R a b f) := by
  have h : (rowGen R (n := n + 1) a b).comp (rename (colEmb r n)) =
      (Polynomial.mapAlgHom (rename (colEmb r n))).comp (rowGen R (n := n) a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Polynomial.coe_mapAlgHom, Polynomial.map_add,
      Polynomial.map_C, colEmb]
    split_ifs <;> simp [colEmb]
  have h2 := congrArg (fun φ => φ f) h
  simpa [Polynomial.coe_mapAlgHom] using h2

theorem rowDiv_rename (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (rename (colEmb r n) f) = rename (colEmb r n) (rowDiv R a b k f) := by
  unfold rowDiv
  rw [rowGen_rename, Polynomial.coeff_map]
  rfl

theorem applyWord_rename (R : Type) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R w (rename (colEmb r n) f) = rename (colEmb r n) (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, rowDiv_rename]

theorem lpMinor_rename (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (hr : s ≤ n + 1) (hn : s ≤ n) :
    lpMinor R (r := n + 1) (n := n + 1) s hr (by omega) =
      rename (colEmb (n + 1) n) (lpMinor R (r := n + 1) (n := n) s hr hn) := by
  unfold lpMinor
  rw [show (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) =
      (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _) from rfl,
    AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, colEmb]
  rfl

theorem hw_rename (R : Type) [CommRing R] {n : ℕ} (ν : Fin (n + 1) → ℕ) (hlast : ν (Fin.last n) = 0) :
    hw R (r := n + 1) (n := n + 1) le_rfl ν =
      rename (colEmb (n + 1) n) (hw R (r := n + 1) (n := n) (Nat.le_succ n) (fun s => ν s.castSucc)) := by
  unfold hw
  rw [Fin.prod_univ_castSucc, map_prod]
  have hl : ν (Fin.last n) - nuNext ν (Fin.last n) = 0 := by rw [hlast]; simp
  rw [hl, pow_zero, mul_one]
  apply Finset.prod_congr rfl
  intro s _
  rw [map_pow]
  have hexp : nuNext ν s.castSucc = nuNext (fun s => ν s.castSucc) s := by
    unfold nuNext
    by_cases h : s.val + 1 < n
    · rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega), dif_pos h]
      rfl
    · rw [dif_neg h]
      have hs : s.val + 1 = n := by omega
      rw [dif_pos (by simp only [Fin.val_castSucc] <;> omega)]
      have : (⟨(s.castSucc : Fin (n + 1)).val + 1, by simp only [Fin.val_castSucc] <;> omega⟩ : Fin (n + 1)) = Fin.last n :=
        Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last] <;> omega)
      rw [this, hlast]
  rw [hexp]
  congr 1
  exact lpMinor_rename R (s.val + 1) (by omega) (by omega)

theorem natW_last {n : ℕ} (lam : DomWeight (n + 1)) : lam.natW (Fin.last n) = 0 := by
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos (Nat.succ_pos n)]
  have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [this]
  simp

theorem delSq_eq_map (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight (n + 1)) :
    delSq R (n + 1) lam =
      (weyl R (n + 1) n (Nat.le_succ n) (fun s => lam.natW s.castSucc)).map
        (rename (colEmb (n + 1) n) : MvPolynomial (Fin (n + 1) × Fin n) R →ₐ[R] _).toLinearMap := by
  unfold delSq weyl
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext w
  change applyWord R w (hw R le_rfl lam.natW) =
    rename (colEmb (n + 1) n) (applyWord R w (hw R (Nat.le_succ n) fun s => lam.natW s.castSucc))
  rw [← applyWord_rename, ← hw_rename R lam.natW (natW_last lam)]

theorem rowAct_rename (R : Type) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowAct R g (rename (colEmb r n) f) = rename (colEmb r n) (rowAct R g f) := by
  have h : (rowAct R (n := n + 1) g).comp (rename (colEmb r n)) =
      (rename (colEmb r n)).comp (rowAct R (n := n) g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct, colEmb, map_sum]
  exact congrArg (fun φ => φ f) h

theorem blockMat_eq_extM {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : blockMat g = Formalism.BranchingDeterminantCap.extM ℂ g := by
  ext a b
  unfold blockMat Formalism.BranchingDeterminantCap.extM
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply, finSumFinEquiv_symm_last, Fin.ext_iff]
    omega
  · simp [Matrix.reindex_apply]

theorem blockMat_transpose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).transpose = blockMat g.transpose := by
  unfold blockMat
  rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

theorem sqAct_of_last_zero (R : Type) [CommRing R] {n : ℕ} (lt : DomWeight (n + 1))
    (h0 : lt.w (Fin.last n) = 0) (H : GL (Fin (n + 1)) R) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R) :
    sqAct R (n + 1) lt H f = rowAct R (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R).transpose f := by
  have hd : lt.detShift = 0 := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos n)]
    have : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    rw [this, h0]
  unfold sqAct detPow
  rw [hd, zpow_zero, Units.val_one, one_smul]

theorem fockF_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (rename e f) (rename e g) = Formalism.REAL.fockF f g := by
  classical
  unfold Formalism.REAL.fockF
  rw [support_rename_of_injective he, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  have hp := Finsupp.prod_mapDomain_index_inj (s := α) (h := fun (_ : τ) (v : ℕ) => v.factorial) he
  unfold Finsupp.prod at hp
  rw [hp]

theorem colEmb_inj (r n : ℕ) : Function.Injective (colEmb r n) := by
  intro v w h
  simp only [colEmb, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castSucc_injective _ h.2)

theorem colAddGen_last_rename (R : Type) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n) (rename (colEmb r n) f) = rename some (rename (colEmb r n) f) := by
  have h : (colAddGen R (r := r) l (Fin.last n)).comp (rename (colEmb r n)) =
      (rename some).comp (rename (colEmb r n)) := by
    apply MvPolynomial.algHom_ext
    intro v
    have hv : (colEmb r n v).2 ≠ Fin.last n := Fin.castSucc_ne_last v.2
    simp [colAddGen, hv]
  exact congrArg (fun φ => φ f) h

theorem colAddGen_castSucc_rename (R : Type) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc (rename (colEmb r n) f) =
      rename (Option.map (colEmb r n)) (colAddGen R l j f) := by
  have h : (colAddGen R (r := r) l.castSucc j.castSucc).comp (rename (colEmb r n)) =
      (rename (Option.map (colEmb r n))).comp (colAddGen R l j) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, colAddGen, aeval_X]
    by_cases hv : v.2 = j
    · have hv' : (colEmb r n v).2 = j.castSucc := by simp [colEmb, hv]
      rw [if_pos hv', if_pos hv]
      simp [colEmb]
    · have hv' : (colEmb r n v).2 ≠ j.castSucc := by
        simp only [colEmb, ne_eq, Fin.castSucc_inj]
        exact hv
      rw [if_neg hv', if_neg hv]
      simp
  exact congrArg (fun φ => φ f) h

theorem rename_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} (ν : Fin (n + 1) → ℕ) (hlast : ν (Fin.last n) = 0)
    (f : MvPolynomial (Fin (n + 1) × Fin n) R) (hf : f ∈ dualWeyl R (n + 1) n (fun s => ν s.castSucc)) :
    rename (colEmb (n + 1) n) f ∈ dualWeyl R (n + 1) (n + 1) ν := by
  classical
  unfold dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨hw, hk⟩ := hf
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    intro d hd
    have hmem : d ∈ (rename (colEmb (n + 1) n) f).support := mem_support_iff.mpr hd
    rw [support_rename_of_injective (colEmb_inj _ _), Finset.mem_image] at hmem
    obtain ⟨d', hd', rfl⟩ := hmem
    have h1 := hw (mem_support_iff.mp hd')
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj (colEmb_inj _ _)]
    rw [Finsupp.weight_apply] at h1
    funext t
    rcases Fin.eq_castSucc_or_eq_last t with ⟨i, rfl⟩ | rfl
    · have := congrFun h1 i
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply,
        Fin.castSucc_inj] at this ⊢
      exact this
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, colW, colEmb, Pi.single_apply, hlast]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (Fin.castSucc_ne_last v.2).symm, smul_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hk ⊢
    intro l j hlj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hl : l.val < n := by
        have := Fin.lt_def.mp hlj
        simp only [Fin.val_castSucc] at this
        omega
      have hll : l = (⟨l.val, hl⟩ : Fin n).castSucc := Fin.ext rfl
      have hlt : (⟨l.val, hl⟩ : Fin n) < j' := by
        rw [Fin.lt_def] at hlj ⊢
        simpa using hlj
      rw [hll, colAddGen_castSucc_rename, hk _ j' hlt, rename_rename, rename_rename]
      rfl
    · exact colAddGen_last_rename R l f

theorem scaleMat_eq_zScale (n : ℕ) (T : ℝ) : scaleMat n T = Formalism.BranchingDeterminantCap.zScale n (Real.sqrt T) := rfl

theorem scaleMat_transpose (n : ℕ) (T : ℝ) : (scaleMat n T).transpose = scaleMat n T := by
  unfold scaleMat
  exact Matrix.diagonal_transpose _

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTie
section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latT_step {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.flipTwoThree.LatT (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u i c) :=
  ⟨clsLat_int X u i hi c, clsLat_index X u i hi c⟩

def FramesStep (D : D7) (u : D.what₂.Word) (i : ℕ) : Prop :=
  ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c)
      (D.clsLat u i c') (e c) (e c') → c = c'

def ClauseP (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' (LP c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') →
        c = c'

theorem clsTie_of {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word)
    (hF : ∀ i ≤ D.R.m, FramesStep D u i) (hP : ClauseP D u) : Formalism.MainNotions.flipTwoThree.ClsTie D u :=
  ⟨fun i hi => ⟨fun c => latT_step X u i hi c, hF i hi⟩, hP⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PFrGen
section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

variable {E : Type} [Field E] [NumberField E]

theorem natCast_ne_zero_int (M : ℕ) (hM : M ≠ 0) : ((M : ℕ) : 𝓞 E) ≠ 0 := by
  intro h
  apply hM
  have := congrArg (algebraMap (𝓞 E) E) h
  simpa using this

theorem ideal_gen (M : ℕ) (hM : M ≠ 0) (J : Ideal (𝓞 E)) :
    ∃ a ∈ J, ∀ j ∈ J, ∃ c : 𝓞 E, ∃ j' ∈ J, j = c * a + (M : 𝓞 E) * j' := by
  by_cases hJ : J = ⊥
  · refine ⟨0, zero_mem _, fun j hj => ⟨0, 0, zero_mem _, ?_⟩⟩
    rw [hJ, Ideal.mem_bot] at hj
    simp [hj]
  · have hM' := natCast_ne_zero_int (E := E) M hM
    have hle : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≤ J := Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)
    have hne : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≠ 0 := by
      intro h
      rw [Ideal.zero_eq_bot, Ideal.mul_eq_bot] at h
      rcases h with h | h
      · exact hM' (Ideal.span_singleton_eq_bot.1 h)
      · exact hJ h
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    refine ⟨a, haJ, fun j hj => ?_⟩
    rw [← ha, Submodule.mem_sup] at hj
    obtain ⟨i, hi, s, hs, rfl⟩ := hj
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.1 hi
    exact ⟨c, z, hz, by ring⟩

theorem clear_fg (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ p ∈ P, ∃ q : 𝓞 E, (d : E) * p = q := by
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) s
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun p hp => ?_⟩
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨q, hq⟩ := hbs p hp
    refine ⟨q, ?_⟩
    have hq' : (q : E) = (b : E) * p := by
      have := hq
      rw [Algebra.smul_def] at this
      exact this
    exact hq'.symm
  | zero => exact ⟨0, by simp⟩
  | add p p' _ _ h h' =>
    obtain ⟨q, hq⟩ := h
    obtain ⟨q', hq'⟩ := h'
    exact ⟨q + q', by push_cast; linear_combination hq + hq'⟩
  | smul a p _ h =>
    obtain ⟨q, hq⟩ := h
    refine ⟨a * q, ?_⟩
    show (b : E) * ((a : E) * p) = ((a * q : 𝓞 E) : E)
    push_cast
    linear_combination (a : E) * hq

theorem sub_gen (M : ℕ) (hM : M ≠ 0) (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ a ∈ P, ∀ p ∈ P, ∃ c : 𝓞 E, ∃ p' ∈ P, p = c • a + (M : E) • p' := by
  obtain ⟨d, hd, hdP⟩ := clear_fg P hP
  have hd' : (d : E) ≠ 0 := by
    intro h; apply hd; exact_mod_cast h
  let J : Ideal (𝓞 E) :=
    { carrier := {q | ∃ p ∈ P, (q : E) = (d : E) * p}
      add_mem' := by
        rintro q q' ⟨p, hp, hq⟩ ⟨p', hp', hq'⟩
        exact ⟨p + p', add_mem hp hp', by push_cast; linear_combination hq + hq'⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c q ⟨p, hp, hq⟩
        refine ⟨c • p, Submodule.smul_mem _ c hp, ?_⟩
        show ((c * q : 𝓞 E) : E) = (d : E) * ((c : E) * p)
        push_cast
        linear_combination (c : E) * hq }
  obtain ⟨a', ⟨pa, hpa, ha'⟩, hgen⟩ := ideal_gen M hM J
  refine ⟨pa, hpa, fun p hp => ?_⟩
  obtain ⟨q, hq⟩ := hdP p hp
  obtain ⟨c, j', ⟨pj, hpj, hj'⟩, hcj⟩ := hgen q ⟨p, hp, hq.symm⟩
  refine ⟨c, pj, hpj, ?_⟩
  have h1 : (d : E) * p = (d : E) * ((c : E) * pa + (M : E) * pj) := by
    have h3 : (q : E) = (c : E) * (a' : E) + (M : E) * (j' : E) := by rw [hcj]; push_cast; ring
    linear_combination hq + h3 + (c : E) * ha' + (M : E) * hj'
  have h2 := mul_left_cancel₀ hd' h1
  rw [h2, Algebra.smul_def, smul_eq_mul]

def snoc0 (r : ℕ) : (Fin r → E) →ₗ[E] (Fin (r + 1) → E) where
  toFun y i := if h : (i : ℕ) < r then y ⟨i, h⟩ else 0
  map_add' y y' := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]
  map_smul' c y := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]

theorem snoc_zero_castSucc (r : ℕ) (y : Fin r → E) (j : Fin r) : snoc0 r y j.castSucc = y j := by
  simp [snoc0]

theorem snoc_zero_last (r : ℕ) (y : Fin r → E) : snoc0 r y (Fin.last r) = 0 := by
  simp [snoc0]

theorem snoc_zero_injective (r : ℕ) : Function.Injective (snoc0 (E := E) r) := by
  intro y y' h
  funext j
  have := congrFun h j.castSucc
  rwa [snoc_zero_castSucc, snoc_zero_castSucc] at this

theorem genMod_fg (M : ℕ) (hM : M ≠ 0) : ∀ (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → GenMod Λ M := by
  intro r
  induction r with
  | zero =>
    intro Λ _
    refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun x _ => ⟨0, 0, zero_mem _, ?_⟩⟩
    exact Subsingleton.elim _ _
  | succ r ih =>
    intro Λ hΛ
    haveI : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian _ hΛ

    let Λ0 : Submodule (𝓞 E) (Fin r → E) := Λ.comap ((snoc0 r).restrictScalars (𝓞 E))
    let φ : Λ0 →ₗ[𝓞 E] Λ :=
      { toFun := fun x => ⟨snoc0 r (x : Fin r → E), x.2⟩
        map_add' := fun x y => by ext1; simp
        map_smul' := fun a x => by
          ext1
          show snoc0 r (a • (x : Fin r → E)) = a • snoc0 r (x : Fin r → E)
          rw [← algebraMap_smul E a (x : Fin r → E), map_smul, algebraMap_smul] }
    have hφ : Function.Injective φ := by
      intro x y h
      exact Subtype.ext (snoc_zero_injective r (congrArg Subtype.val h))
    haveI : IsNoetherian (𝓞 E) Λ0 := isNoetherian_of_injective φ hφ
    have hΛ0 : Λ0.FG := (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)
    obtain ⟨b0, hb0, hgen0⟩ := ih Λ0 hΛ0

    let P : Submodule (𝓞 E) E := Λ.map ((LinearMap.proj (Fin.last r) : (Fin (r + 1) → E) →ₗ[E] E).restrictScalars (𝓞 E))
    obtain ⟨a, ⟨xa, hxa, hxae⟩, hgenP⟩ := sub_gen M hM P (hΛ.map _)
    simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxae
    refine ⟨Fin.lastCases xa (fun j => snoc0 r (b0 j)), fun i => ?_, fun x hx => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last]; exact hxa
      · simp only [Fin.lastCases_castSucc]; exact hb0 j
    · obtain ⟨c, p', ⟨xj, hxj, hxje⟩, hce⟩ := hgenP (x (Fin.last r)) ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxje
      set y : Fin (r + 1) → E := x - c • xa - (M : E) • xj with hy
      have hyΛ : y ∈ Λ := by
        refine sub_mem (sub_mem hx (Submodule.smul_mem _ c hxa)) ?_
        have : (M : E) • xj = ((M : ℕ) : 𝓞 E) • xj := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        rw [this]
        exact Submodule.smul_mem _ _ hxj
      have hylast : y (Fin.last r) = 0 := by
        rw [hy]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hce, hxae, hxje, Algebra.smul_def, Algebra.smul_def]
        simp
      set y0 : Fin r → E := fun j => y j.castSucc with hy0
      have hyy : snoc0 r y0 = y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [snoc_zero_last, hylast]
        · rw [snoc_zero_castSucc]
      have hy0Λ : y0 ∈ Λ0 := by
        show snoc0 r y0 ∈ Λ
        rw [hyy]; exact hyΛ
      obtain ⟨c', z0, hz0, hz0e⟩ := hgen0 y0 hy0Λ
      refine ⟨Fin.lastCases c c', xj + snoc0 r z0, add_mem hxj hz0, ?_⟩
      have hx' : x = c • xa + (M : E) • xj + snoc0 r y0 := by
        rw [hyy, hy]; abel
      rw [hx', hz0e, Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, map_add, map_sum, smul_add]
      have hs : ∀ j, snoc0 r (c' j • b0 j) = c' j • snoc0 r (b0 j) := by
        intro j
        rw [← algebraMap_smul E (c' j) (b0 j), map_smul, algebraMap_smul]
      simp only [hs, map_smul]
      abel

theorem genMod (M : ℕ) (hM : M ≠ 0) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Module.Finite (𝓞 E) Λ) :
    GenMod Λ M :=
  genMod_fg M hM r Λ (Module.Finite.iff_fg.1 hΛ)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
end

