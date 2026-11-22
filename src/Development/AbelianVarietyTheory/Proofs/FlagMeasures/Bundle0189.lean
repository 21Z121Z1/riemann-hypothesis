import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamental
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEqv

section Count

variable {α : Type} {R : α → α → Prop}

theorem cntCl_eq_encard (hR : Equivalence R) (X : Set α) :
    cntCl X R = ((fun a => {b | R a b}) '' X).encard := by

  have hset : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} =
      (fun O => {b | b ∈ O ∧ b ∈ X}) '' ((fun a => {b | R a b}) '' X) := by
    ext O
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨{b | R a b}, ⟨a, ha, rfl⟩, by ext b; simp [and_comm]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by ext b; simp [and_comm]⟩
  rw [cntCl, hset]
  apply Set.InjOn.encard_image
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ hEq
  have hEq' : {b | b ∈ {b | R a b} ∧ b ∈ X} = {b | b ∈ {b | R a' b} ∧ b ∈ X} := hEq
  have hmem : a' ∈ {b | b ∈ {b | R a b} ∧ b ∈ X} := by
    rw [hEq']
    exact ⟨hR.refl a', ha'⟩
  have haa' : R a a' := hmem.1
  ext b
  exact ⟨fun hb => hR.trans (hR.symm haa') hb, fun hb => hR.trans haa' hb⟩

theorem encard_biUnion_le' {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    (⋃ i ∈ s, Y i).encard ≤ ∑ i ∈ s, (Y i).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

theorem cntCl_le_sum (hR : Equivalence R) {ι : Type} (s : Finset ι) (X : Set α) (Y : ι → Set α)
    (h : ∀ a ∈ X, ∃ i ∈ s, ∃ b ∈ Y i, R a b) : cntCl X R ≤ ∑ i ∈ s, cntCl (Y i) R := by
  simp only [cntCl_eq_encard hR]
  calc ((fun a => {b | R a b}) '' X).encard
      ≤ (⋃ i ∈ s, (fun a => {b | R a b}) '' Y i).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨i, hi, b, hb, hab⟩ := h a ha
        refine Set.mem_biUnion hi ⟨b, hb, ?_⟩
        ext c
        exact ⟨fun hc => hR.trans hab hc, fun hc => hR.trans (hR.symm hab) hc⟩
    _ ≤ ∑ i ∈ s, ((fun a => {b | R a b}) '' Y i).encard := encard_biUnion_le' s _

end Count

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

theorem mem_gmap (g : S.V ≃ₗ[E] S.V) (x : S.V) : x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

theorem aut_mem_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (x : S.V) : n x ∈ Λ ↔ x ∈ Λ := by
  have hx := mem_gmap (Λ := Λ) n (n x)
  rw [hn.2, LinearEquiv.symm_apply_apply] at hx
  exact hx

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

theorem X_le_orth : Xsp F ≤ orth S (Xsp F) := by

  have key : ∀ a, Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := fun a => by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.fl.e_iso a b
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have key2 : Xsp F ≤ LinearMap.ker (S.hT.flip y) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key a hy
  simpa using key2 hx

theorem symm_sub_mem (n : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) : ∀ x ∈ B, n.symm x - x ∈ A := by
  intro x hx

  have hmap : ∀ y ∈ B, n y ∈ B := fun y hy => by simpa using B.add_mem (hAB (h y hy)) hy
  have hinj : Function.Injective (n.toLinearMap.restrict hmap) := fun a b hab =>
    Subtype.ext (n.injective (congrArg Subtype.val hab))
  obtain ⟨⟨y, hy⟩, hyx⟩ := LinearMap.surjective_of_injective hinj ⟨x, hx⟩
  have hny : n y = x := congrArg Subtype.val hyx
  have hy' : n.symm x = y := by rw [← hny, LinearEquiv.symm_apply_apply]
  rw [hy', ← neg_sub]
  have hxy := h y hy
  rw [hny] at hxy
  exact A.neg_mem hxy

theorem trans_sub_mem (n m : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) (h' : ∀ x ∈ B, m x - x ∈ A) : ∀ x ∈ B, (m * n) x - x ∈ A := by
  intro x hx
  have hnx : n x ∈ B := by simpa using B.add_mem (hAB (h x hx)) hx
  show m (n x) - x ∈ A
  have e : m (n x) - x = (m (n x) - n x) + (n x - x) := by abel
  rw [e]
  exact A.add_mem (h' _ hnx) (h x hx)

theorem one_mem_NLam : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).one_mem, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · ext x
    rw [mem_gmap]
    rfl
  · simp
  · simp

theorem mul_mem_NLam {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : m * n ∈ NLam Λ F := by
  have hsymm : ∀ {k : S.V ≃ₗ[E] S.V}, IsAutLam S Λ k → ∀ y, k.symm y ∈ Λ ↔ y ∈ Λ := fun hk y => by
    rw [← aut_mem_iff hk, LinearEquiv.apply_symm_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hm.1.1 hn.1.1, ?_⟩,
    fun j => trans_sub_mem n m (Xflag_mono j) (hn.2.1 j) (hm.2.1 j),
    trans_sub_mem n m X_le_orth hn.2.2 hm.2.2⟩
  ext x
  rw [mem_gmap]
  exact (hsymm hn.1 _).trans (hsymm hm.1 _)

theorem symm_mem_NLam {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hn.1.1, ?_⟩,
    fun j => symm_sub_mem n (Xflag_mono j) (hn.2.1 j), symm_sub_mem n X_le_orth hn.2.2⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm]
  exact aut_mem_iff hn.1 x

theorem frameAct_one {k : ℕ} (f : Fin k → S.V) : frameAct f 1 = f := by
  funext b
  simp only [frameAct]
  rw [Finset.sum_eq_single b (fun a _ hab => by rw [Matrix.one_apply_ne hab]; simp)
    (fun hb => absurd (Finset.mem_univ b) hb), Matrix.one_apply_eq]
  simp

theorem frameAct_mul {k : ℕ} (f : Fin k → S.V) (ξ η : Matrix (Fin k) (Fin k) (𝓞 E)) :
    frameAct (frameAct f ξ) η = frameAct f (ξ * η) := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem map_frameAct {k : ℕ} (n : S.V ≃ₗ[E] S.V) (f : Fin k → S.V) (ξ : Matrix (Fin k) (Fin k) (𝓞 E)) :
    (fun a => n (frameAct f ξ a)) = frameAct (fun a => n (f a)) ξ := by
  funext b
  simp only [frameAct, map_sum, map_smul]

theorem uni_mul {k : ℕ} {O : Type} [CommRing O] {ξ η : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a b, b < a → η a b = 0) (a : Fin k) :
    (ξ * η) a a = ξ a a * η a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with hc | hc
    · rw [h1 a c hc, zero_mul]
    · rw [h2 c a hc, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem uni_inv {k : ℕ} {O : Type} [CommRing O] {ξ : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    ∃ η : Matrix (Fin k) (Fin k) O, (∀ a b, b < a → η a b = 0) ∧ (∀ a, η a a = 1) ∧ ξ * η = 1 := by

  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hu : IsUnit ξ.det := by
    rw [hdet]
    exact isUnit_one
  let _ := Matrix.invertibleOfIsUnitDet ξ hu
  have hinv : ξ⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ hu
  refine ⟨ξ⁻¹, fun a b hab => hinv hab, fun a => ?_, hmul⟩
  have hd := uni_mul h1 (fun a b hab => hinv hab) a
  rw [hmul, Matrix.one_apply_eq, h2, one_mul] at hd
  exact hd.symm

end Grp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TEqv_equivalence (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : Fg D T) :
    Equivalence (TEqv D Λ F (T' := T')) := by
  refine ⟨fun F' => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h h' => ?_⟩
  · refine ⟨1, one_mem_NLam, 1, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, ?_⟩
    rw [frameAct_one]
    rfl
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨η, hη1, hη2, hξη⟩ := uni_inv h1 h2
    refine ⟨n.symm, symm_mem_NLam hn, η, hη1, hη2, ?_⟩
    rw [hfr, map_frameAct]
    simp only [LinearEquiv.symm_apply_apply]
    rw [frameAct_mul, hξη, frameAct_one]
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨m, hm, ζ, k1, k2, hfr'⟩ := h'
    refine ⟨m * n, mul_mem_NLam hn hm, ξ * ζ, fun a b hab => ?_, fun a => ?_, ?_⟩
    · exact Matrix.BlockTriangular.mul (b := id) (fun i j hij => h1 i j hij) (fun i j hij => k1 i j hij) hab
    · rw [uni_mul h1 k1 a, h2, k2, one_mul]
    · rw [hfr', hfr, map_frameAct, frameAct_mul]
      rfl

end GlobalTheory.LoopC.FrEqv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_biorth {E : Type} [Field E] {n m : ℕ} {r : ℕ → ℕ}
    (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (hr : ∀ b, m ≤ b → r b = 0)
    (hn : n = ∑ b ∈ Finset.range m, r b)
    (hs : ∀ y : Fin n → E, ∃ u : ∀ b, Fin (r b) → E, y = ∑ b ∈ Finset.range m, T b *ᵥ u b) :
    ∃ T' : ∀ b, Matrix (Fin (r b)) (Fin n) E, Biorth r m T T' := by
  classical
  let Φ : ((b : Fin m) → Fin (r b) → E) →ₗ[E] (Fin n → E) :=
    ∑ b : Fin m, (T b).mulVecLin ∘ₗ LinearMap.proj b
  have hΦ : ∀ u : ∀ b, Fin (r b) → E, Φ (fun b => u b) = ∑ b ∈ Finset.range m, T b *ᵥ u b := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun b => T b *ᵥ u b)]
    simp [Φ]
  have hsurj : Function.Surjective Φ := fun y => by
    obtain ⟨u, hu⟩ := hs y
    exact ⟨_, (hΦ u).trans hu.symm⟩
  have hinj : Function.Injective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hn, Fin.sum_univ_eq_sum_range]
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let T' : ∀ b, Matrix (Fin (r b)) (Fin n) E := fun b =>
    if h : b < m then LinearMap.toMatrix'
      ((LinearMap.proj (⟨b, h⟩ : Fin m) : ((b : Fin m) → Fin (r b) → E) →ₗ[E] _) ∘ₗ e.symm.toLinearMap)
    else 0
  have hemp : ∀ b, ¬ b < m → IsEmpty (Fin (r b)) := fun b hb => by
    rw [hr b (by omega)]; infer_instance
  have hT' : ∀ (b : Fin m) y, T' b *ᵥ y = e.symm y b := fun b y => by
    simp only [T', dif_pos b.2]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have H1 : ∀ (u : ∀ b, Fin (r b) → E) b, T' b *ᵥ (∑ c ∈ Finset.range m, T c *ᵥ u c) = u b := by
    intro u b
    by_cases hb : b < m
    · rw [hT' ⟨b, hb⟩, ← hΦ]
      exact congrFun (e.symm_apply_apply _) _
    · have := hemp b hb
      exact Subsingleton.elim _ _
  have H2 : ∀ b c v, T' b *ᵥ (T c *ᵥ v) = (Pi.single c v : ∀ b, Fin (r b) → E) b := by
    intro b c v
    rw [← H1 (Pi.single c v) b]
    congr 1
    by_cases hc : c < m
    · rw [Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd])
        (fun h => absurd (Finset.mem_range.2 hc) h)]
      simp
    · have := hemp c hc
      obtain rfl : v = 0 := Subsingleton.elim _ _
      simp
  refine ⟨T', fun b => ?_, fun b c hbc => ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, H2]; simp [Pi.single_eq_of_ne hbc]
  · refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := hs y
    simp only [Matrix.toLin'_apply]
    rw [Matrix.sum_mulVec, Matrix.one_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Matrix.mulVec_mulVec, H1]

theorem exists_biorth_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  intro E _ _ n m F r hmono h0 hm hL hsat hrk
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hmono h
    · exact (hm b h).le
  have key : ∀ b, ∃ A : Submodule (𝓞 E) (Fin n → E), A ⊓ F b = ⊥ ∧ A ⊔ F b = F (b + 1) := by
    intro b
    refine exists_compl_of_saturated _ _ (hmono b.le_succ) (Submodule.FG.of_le hL.fg (hle _)) ?_
    intro c y hc hy hcy
    apply hsat _ y (hle _ hy)
    have hc' : (c : E) ≠ 0 := by simpa using hc
    rw [← Submodule.smul_mem_iff _ hc']
    exact Submodule.subset_span hcy
  choose A hA1 hA2 using key
  have hAF : ∀ b, A b ≤ F (b + 1) := fun b => hA2 b ▸ le_sup_left
  have hAr : ∀ b, Formalism.HN.rkK (A b) = r b := fun b => by
    have := AdaptedExists.rkK_add (hA1 b)
    rw [hA2, hrk] at this
    omega
  choose Λ T hΛ hT using fun b => AdaptedExists.exists_model (A b)
    (Submodule.FG.of_le hL.fg ((hAF b).trans (hle _))) (hAr b)
  have hdec : ∀ k, ∀ y ∈ F k, ∃ u : ∀ b, Fin (r b) → E, (∀ b, u b ∈ Λ b) ∧
      y = ∑ b ∈ Finset.range k, T b *ᵥ u b := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [h0, Submodule.mem_bot] at hy
      exact ⟨0, fun b => zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      rw [← hA2] at hy
      obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨v, hv, rfl⟩ := (hT k a).1 ha
      obtain ⟨u, hu, rfl⟩ := ih z hz
      refine ⟨Function.update u k v, fun b => ?_, ?_⟩
      · by_cases hb : b = k
        · subst hb; simpa using hv
        · rw [Function.update_of_ne hb]; exact hu b
      · rw [Finset.sum_range_succ, add_comm, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Function.update_of_ne (Finset.mem_range.1 hc).ne]
  have hr0 : ∀ b, m ≤ b → r b = 0 := fun b hb => by
    have := hrk b
    rw [hm b hb, hm (b + 1) (by omega)] at this
    omega
  have hsum : ∀ k, Formalism.HN.rkK (F k) = ∑ b ∈ Finset.range k, r b := by
    intro k
    induction k with
    | zero => rw [h0]; simp [Formalism.HN.rkK]
    | succ k ih => rw [hrk, ih, Finset.sum_range_succ]
  have hn : n = ∑ b ∈ Finset.range m, r b := by
    rw [← hsum, Formalism.HN.rkK, hL.span_eq_top]
    simp
  obtain ⟨T', hB⟩ := exists_biorth T hr0 hn (fun y => by
    obtain ⟨c, hc, hcy⟩ := AdaptedExists.exists_smul_mem (L := F m) (x := y)
      (by rw [hL.span_eq_top]; trivial)
    obtain ⟨u, -, hu⟩ := hdec m _ hcy
    have hc' : (c : E) ≠ 0 := by simpa using hc
    refine ⟨fun b => (c : E)⁻¹ • u b, ?_⟩
    simp only [Matrix.mulVec_smul]
    rw [← Finset.smul_sum, ← hu, eq_inv_smul_iff₀ hc']
    rfl)
  refine ⟨T, T', Λ, hB, hΛ, fun k y => ⟨fun hy b => ?_, fun hy => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := hdec k y hy
    have h1 : T' b *ᵥ (∑ c ∈ Finset.range k, T c *ᵥ u c) = if b < k then u b else 0 := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec]
      split_ifs with hb
      · rw [Finset.sum_eq_single b (fun c _ hc => by rw [hB.2.1 b c hc.symm, Matrix.zero_mulVec])
          (fun h => absurd (Finset.mem_range.2 hb) h), hB.1, Matrix.one_mulVec]
      · refine Finset.sum_eq_zero fun c hc => ?_
        rw [hB.2.1 b c (by have := Finset.mem_range.1 hc; omega), Matrix.zero_mulVec]
    rw [h1]
    refine ⟨?_, fun h => if_neg (by omega)⟩
    split_ifs
    · exact hu b
    · exact zero_mem _
  · have h1 : y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hB.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · rw [(hy b).2 hb, Matrix.mulVec_zero]; exact zero_mem _
    · exact hmono (show b + 1 ≤ k by omega) (hAF b ((hT b _).2 ⟨_, (hy b).1, rfl⟩))

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjGaugeInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rw [hH]
  exact h2

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hu := Continuous.units_map _ hc
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rw [hf]
  exact key

theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  first | exact @GlobalTheory.LatDom.exists_cone_domain | exact GlobalTheory.LatDom.exists_cone_domain | (intros; apply GlobalTheory.LatDom.exists_cone_domain <;> assumption)
end

