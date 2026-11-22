import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.EtaleCohomology.EtaleSheaves.Bundle0020
import Development.EtaleCohomology.EtaleSheaves.ZarIndPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0017
import Development.EtaleCohomology.EtaleSheaves.Bundle0026

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltGenPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.FiltGenPf

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma ofHom_comp_fromSingleMk {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {q m : ℤ}
    (g : Y ⟶ I.X q) (hq : k + m = q) :
    (Cochain.ofHom ((singleFunctor C k).map h)).comp
      (Cochain.fromSingleMk (p := k) g hq) (zero_add m) = Cochain.fromSingleMk (p := k) (h ≫ g) hq := by
  ext p q' hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by lia
    rw [Cochain.fromSingleMk_v, Cochain.fromSingleMk_v]
    change ((HomologicalComplex.single C (ComplexShape.up ℤ) p).map h).f p ≫ _ = _
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

lemma smul_fromSingleMk {X : C} {I : CochainComplex C ℤ} (k : ℤ) (ε : ℤˣ) {q m : ℤ}
    (g : X ⟶ I.X q) (hq : k + m = q) :
    ε • Cochain.fromSingleMk (p := k) g hq = Cochain.fromSingleMk (p := k) (ε • g) hq := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h <;> simp

lemma desc_eta {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n : ℤ} (hmn : m + 1 = n)
    (c : Cochain (mappingCone φ) I n) :
    c = mappingCone.descCochain φ ((mappingCone.inl φ).comp c (by lia))
      ((Cochain.ofHom (mappingCone.inr φ)).comp c (zero_add n)) hmn := by
  rw [mappingCone.ext_cochain_from_iff φ m n hmn]
  simp

lemma δ_desc_fromSingle {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {m m' qa qb qc : ℤ}
    (hm : m + 1 = m') (a : X ⟶ I.X qa) (b : Y ⟶ I.X qb) (ha : k + (m - 1) = qa) (hb : k + m = qb)
    (hc : k + m' = qc) :
    δ m m' (mappingCone.descCochain ((singleFunctor C k).map h) (Cochain.fromSingleMk a ha)
      (Cochain.fromSingleMk b hb) (by lia)) =
    mappingCone.descCochain ((singleFunctor C k).map h)
      (Cochain.fromSingleMk (a ≫ I.d qa qb + m'.negOnePow • (h ≫ b)) hb)
      (Cochain.fromSingleMk (b ≫ I.d qb qc) hc) (by lia) := by
  rw [mappingCone.δ_descCochain _ _ _ _ m' hm, Cochain.δ_fromSingleMk _ _ m qb hb,
    Cochain.δ_fromSingleMk _ _ m' qc hc, ofHom_comp_fromSingleMk, smul_fromSingleMk,
    ← Cochain.fromSingleMk_add]
  rfl

lemma level_of {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (f : K.X k ⟶ I.X (k + (n - 1))) (g : L.X k ⟶ I.X (k + n))
    (hg : g ≫ I.d (k + n) (k + (n + 1)) = 0)
    (hf : f ≫ I.d (k + (n - 1)) (k + n) + (n + 1).negOnePow • (φ.f k ≫ g) = 0) :
    ∃ (a : K.X k ⟶ I.X (k + (n - 1 - 1))) (b : L.X k ⟶ I.X (k + (n - 1))),
      f = a ≫ I.d _ _ + n.negOnePow • (φ.f k ≫ b) ∧ g = b ≫ I.d _ _ := by
  have hk' : Subsingleton (CohomologyClass (mappingCone ((singleFunctor C k).map (φ.f k))) I n) := hk
  let w : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I n := mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
    (Cochain.fromSingleMk f (show k + (n - 1) = k + (n - 1) from rfl))
    (Cochain.fromSingleMk g (show k + n = k + n from rfl)) (by lia)
  have hw : δ n (n + 1) w = 0 := by
    simp only [w]
    rw [δ_desc_fromSingle k (φ.f k) rfl f g rfl rfl rfl, hf, hg]
    simp [mappingCone.descCochain]
  have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk w (n + 1) rfl hw)) 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by lia)] at h0
  obtain ⟨c, hc⟩ := h0
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c (show -1 + (n - 1) = n - 1 - 1 by lia)) (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c (zero_add (n - 1))) (k + (n - 1)) rfl
  rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by lia) c, ← ha, ← hb,
    δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by lia) a b (by lia) rfl rfl] at hc
  refine ⟨a, b, ?_, ?_⟩
  · have := congrArg (fun x => (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp x (show -1 + n = n - 1 by lia)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inl_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) this
    simpa using this.symm
  · have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp x (zero_add n)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inr_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) this
    simpa using this.symm

lemma δ_desc {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n n' : ℤ} (h : m + 1 = n) (hn' : n + 1 = n')
    (α : Cochain K I m) (β : Cochain L I n) :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) :=
  mappingCone.δ_descCochain φ α β h n' hn'

def V {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ) (z : Cochain (mappingCone φ) I n) : Prop :=
  (∀ p q (hpq : p + (n - 1) = q), k < p →
    ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v p q hpq = 0) ∧
  (∀ p q (hpq : p + n = q), k < p →
    ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0)

lemma step {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (z : Cochain (mappingCone φ) I n) (hz : δ n (n + 1) z = 0) (hV : V φ k n z) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨hV1, hV2⟩ := hV
  have hzd := desc_eta φ (show n - 1 + 1 = n by omega) z
  generalize hα : (mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega) = α at hV1 hzd
  generalize hβ : (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n) = β at hV2 hzd
  have hV1' : ∀ p q (hpq : p + (n - 1) = q), k < p → α.v p q hpq = 0 := fun p q hpq h => by
    rw [← hα]; exact hV1 p q hpq h
  have hδ := hz
  rw [hzd, δ_desc φ (by omega) rfl] at hδ
  have e1 : δ (n - 1) n α + (n + 1).negOnePow • (Cochain.ofHom φ).comp β (zero_add n) = 0 := by
    have := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) hδ
    simpa only [mappingCone.inl_descCochain, Cochain.comp_zero] using this
  have e2 : δ n (n + 1) β = 0 := by
    have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr φ)).comp x (zero_add (n + 1))) hδ
    simpa only [mappingCone.inr_descCochain, Cochain.comp_zero] using this
  have hg : β.v k (k + n) rfl ≫ I.d (k + n) (k + (n + 1)) = 0 := by
    have := Cochain.congr_v e2 k (k + (n + 1)) rfl
    rw [δ_v n (n + 1) rfl β k (k + (n + 1)) rfl (k + n) (k + 1) (by omega) rfl, Cochain.zero_v,
      hV2 (k + 1) (k + (n + 1)) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hf : α.v k (k + (n - 1)) rfl ≫ I.d (k + (n - 1)) (k + n) +
      (n + 1).negOnePow • (φ.f k ≫ β.v k (k + n) rfl) = 0 := by
    have := Cochain.congr_v e1 k (k + n) rfl
    rw [Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1) n (by omega) α k (k + n) rfl (k + (n - 1)) (k + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v,
      hV1' (k + 1) (k + n) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  obtain ⟨a, b, ha, hb⟩ := level_of φ k n hk _ _ hg hf
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1))
    (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
      Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1 - 1) (n - 1) (by omega) _ p q hpq (p + (n - 1 - 1)) (p + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.single_v_eq_zero a _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + (n - 1) := by omega
      have h1 : ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) hpq =
        α.v k (k + (n - 1)) hpq := by rw [hα]
      rw [Cochain.single_v, Cochain.single_v, h1, ha]
      simp
    · rw [hV1 p q hpq hkp, Cochain.single_v_eq_zero a _ p _ _ (by omega),
        Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
      Cochain.sub_v,
      δ_v (n - 1) n (by omega) _ p q hpq (p + (n - 1)) (p + 1) (by omega) rfl,
      Cochain.single_v_eq_zero b _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + n := by omega
      have h2 : ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) hpq =
        β.v k (k + n) hpq := by rw [hβ]
      rw [Cochain.single_v, h2, hb]
      simp
    · rw [(show ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0 by rw [hβ]; exact hV2 p q hpq hkp), Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp

theorem FiltGen_of : LateralTheory.E.CechFiltPf.FiltGen.{u, v} := by
  intro C _ _ K L I φ n hK hL hI hlev
  have claim : ∀ m : ℕ, ∀ z : Cochain (mappingCone φ) I n, δ n (n + 1) z = 0 →
      ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (-(m : ℤ)) n (z - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      refine ⟨0, ?_, ?_⟩
      · intro p q hpq hp
        exact (hK p (by omega)).eq_of_src _ _
      · intro p q hpq hp
        exact (hL p (by omega)).eq_of_src _ _
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      obtain ⟨c', hc'⟩ := step φ (-(m : ℤ)) n (hlev _ (by omega)) (z - δ (n - 1) n c)
        (by rw [δ_sub, δ_δ, sub_zero]; exact hz) hc
      refine ⟨c + c', ?_⟩
      have e : (-((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  constructor
  intro x y
  suffices h : ∀ x : CohomologyClass (mappingCone φ) I n, x = 0 by rw [h x, h y]
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z (Cocycle.δ_eq_zero z (n + 1))
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have h0 : (z : Cochain (mappingCone φ) I n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    constructor
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at h0
  exact h0.symm

end LateralTheory.E.FiltGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemPartPf
section
namespace LateralTheory.E.IdemPartPf

open Finset

theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.InjStepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.InjStepPf

def TwoStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ,
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ (U V W : S.Opens) (hV : V ≤ U) (hW : W ≤ U), IsCompact (V : Set S) → IsCompact (W : Set S) →
  ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
  pull _ (sch.map (resO p hV)) _ _ x = 0 → pull _ (sch.map (resO p hW)) _ _ x = 0 →
  pull _ (sch.map (resO p (sup_le hV hW))) _ _ x = 0

def EmptyH : Prop := Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (U : S.Opens), (U : Set S) = ∅ →
  ∀ (i n : ℤ) (x : Ht q (sch.obj (overO p U)) n i), x = 0

variable {X S : Scheme.{0}}

theorem resO_comp (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [resO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Scheme.homOfLE_homOfLE, Category.comp_id]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [resO]

theorem dies_mono {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) (hx : pull _ (sch.map (resO p h2)) _ _ x = 0) :
    pull _ (sch.map (resO p (h1.trans h2))) _ _ x = 0 := by
  rw [← resO_comp p h1 h2, Functor.map_comp, pull_comp, hx, map_zero]

def OverMV : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens),
  ∃ (δX : Ht q (sch.obj (overO p (V ⊓ W))) m i →+ Ht q (sch.obj (overO p (V ⊔ W))) (m + 1) i)
    (δY : Ht q (sch.obj (overO (f ≫ p) (V ⊓ W))) m i →+ Ht q (sch.obj (overO (f ≫ p) (V ⊔ W))) (m + 1) i),
  (∀ x, pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x = 0 →
      pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x = 0 → ∃ w, δX w = x) ∧
  (∀ a b, δX (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b) = 0) ∧
  (∀ w, δY w = 0 → ∃ a b, w = pull _ (sch.map (resO (f ≫ p) (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO (f ≫ p) (inf_le_right : V ⊓ W ≤ W))) _ _ b) ∧
  ∀ w, δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = pull _ (sch.map (fO f p (V ⊔ W))) _ _ (δX w)

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [resO, fO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem pull_fO_res {q : ℕ} {i n : ℤ} {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p h)) _ _ x) =
      pull _ (sch.map (resO (f ≫ p) h)) _ _ (pull _ (sch.map (fO f p U)) _ _ x) := by
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, fO_res]

theorem pull_res_res {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (resO p h1)) _ _ (pull _ (sch.map (resO p h2)) _ _ x) = pull _ (sch.map (resO p (h1.trans h2))) _ _ x := by
  rw [← pull_comp, ← Functor.map_comp, resO_comp]

theorem TwoStep_of (hO : OverMV) : TwoStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hb U V W hV hW hVc hWc x hx hdV hdW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  obtain ⟨δX, δY, e1, e2, e3, e4⟩ := hO hM hH q f p i m V W
  set x' := pull _ (sch.map (resO p (sup_le hV hW))) _ _ x with hx'
  have d1 : pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdV
  have d2 : pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdW
  obtain ⟨w, hw⟩ := e1 x' d1 d2
  have fx' : pull _ (sch.map (fO f p (V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_fO_res, hx, map_zero]
  have hδ : δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = 0 := by rw [e4, hw, fx']
  obtain ⟨a', b', hab⟩ := e3 _ hδ
  obtain ⟨a, rfl⟩ := (hb' V hVc).2 a'
  obtain ⟨b, rfl⟩ := (hb' W hWc).2 b'
  have hI : IsCompact ((V ⊓ W : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
  have hw2 : w = pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b := by
    apply (hb' _ hI).1
    rw [hab, map_sub, pull_fO_res, pull_fO_res]
  rw [← hw, hw2, e2]

theorem InjStep_of (hT : TwoStep) (hE : EmptyH) : InjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_cases hne : (U : Set S) = ∅
  · exact hE hH q p U hne i n x
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.2 hne

  have loc : ∀ s ∈ (U : Set S), ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0 := by
    intro s hs
    obtain ⟨V, hVU, hsV, hd⟩ := (hg s).1 U hs x hx
    obtain ⟨V', hV'B, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hsV
    exact ⟨V', hV'V.trans hVU, hsV', IsAffineOpen.isCompact hV'B, dies_mono p hV'V hVU x hd⟩
  let P : Set S → Prop := fun T => ∃ (V : S.Opens) (h : V ≤ U), T ⊆ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0
  have hP : P (U : Set S) := by
    refine hU.induction_on (p := P) ?_ ?_ ?_ ?_
    · obtain ⟨V, h, _, hc, hd⟩ := loc s0 hs0
      exact ⟨V, h, Set.empty_subset _, hc, hd⟩
    · intro s t hst ⟨V, h, htV, hc, hd⟩
      exact ⟨V, h, hst.trans htV, hc, hd⟩
    · intro s t ⟨V, h, hsV, hc, hd⟩ ⟨W, h', htW, hc', hd'⟩
      refine ⟨V ⊔ W, sup_le h h', ?_, ?_, hT hM hH q f p hq i n hb U V W h h' hc hc' x hx hd hd'⟩
      · exact Set.union_subset_union hsV htW
      · simpa using hc.union hc'
    · intro s hs
      obtain ⟨V, h, hsV, hc, hd⟩ := loc s hs
      exact ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hsV), V, h, subset_rfl, hc, hd⟩
  obtain ⟨V, h, hUV, _, hd⟩ := hP
  have hVU : V = U := le_antisymm h hUV
  subst hVU
  simpa [resO_refl, pull_id] using hd

end LateralTheory.E.InjStepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IterBCPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterBCPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} {a : P' ⟶ P} {q' : P' ⟶ X} {g : X ⟶ S}, IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' a q' g w
    exact IterLine.iso _ (w.isIso_snd_of_isIso he)
  | comp l k hl hk ih =>
    intro X P' a q' g w
    have hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g := IsPullback.of_hasPullback k g
    let m : P' ⟶ pullback k g := pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)
    have hm : q' = m ≫ pullback.snd k g := (pullback.lift_snd _ _ _).symm
    have ht : IsPullback a m l (pullback.fst k g) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb
      rw [← hm]; exact w
    rw [hm]
    exact IterLine.comp m _ (IsLine.bc hl ht) (ih hb)

theorem IterBC_of : IterBC := by
  intro P S X q g hq
  exact iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip

end LateralTheory.E.IterBCPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KerLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KerLocPf

def KillKer : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n, pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ P E (d ≫ e) ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

def PtsEt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y D E : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) (e : D ⟶ E),
  IsUnit (q : A) → LocPts q i φ d → Et e → LocPts q i φ (d ≫ e)

def TruncKer : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ'')) (tw q i) m)) →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n,
    pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 → pull _ (sch.map (Spec.map e)) (tw q i) n x = 0 → x = 0

theorem KerLoc_of (hK : KillKer) (hP : PtsEt) (hT : TruncKer) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow hcok D d hD hpts Y' w φ' hpo
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨E, e, Y'', u, φ'', he, hs, hE, hpo', hxE⟩ :=
    hK hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo x hx
  have hptsE : LocPts q i φ (d ≫ e) := hP hH q i φ d e hq hpts he
  have hpoE : IsPushout φ (d ≫ e) (w ≫ u) φ'' := hpo.paste_vert hpo'
  exact hT hH q i n φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
    (hcok D d hD hpts Y' w φ' hpo) (hcok E (d ≫ e) hE hptsE Y'' (w ≫ u) φ'' hpoE) x hx hxE

end LateralTheory.E.KerLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ChartSurjCut

namespace LateralTheory.E.LCIsoPf

def TwTriv : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), Sec (tw q 0) X ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ x : Sec (tw q 0) X,
      Sec.res f (e X s x) = e Y t (Sec.res f x)

def Tw0 : Prop := ∀ (q : ℕ),
  ∃ c : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → (LocallyConstant T (ZMod q) ≃+ Sec (tw q 0) T),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (hV : IsUnit (q : Γ(V, ⊤))) (hU : IsUnit (q : Γ(U, ⊤))) (a : LocallyConstant U (ZMod q)),
      Sec.res g (c U hU a) = c V hV (a.comap g.base.hom)

def SecIso : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      Sec.res f (e X s g) = e Y t (g.comap f.base.hom)

theorem unit_of {q : ℕ} {S X : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) : IsUnit (q : Γ(X, ⊤)) :=
  (ζ.map s.appTop.hom).2.1

theorem SecIso_of (hT : TwTriv) (h0 : Tw0) : SecIso := by
  intro q i S ζ
  obtain ⟨eT, heT⟩ := hT q i S ζ
  obtain ⟨c, hc⟩ := h0 q
  refine ⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]

theorem SecIso_LCIso (hS : SecIso) : LCIso := by
  intro H q i S ζ
  obtain ⟨eS, heS⟩ := hS q i S ζ
  obtain ⟨-, eA, heA, -⟩ := H.a9 (ZMod q) (tw q i)
  refine ⟨fun X s => (eS X s).trans (eA X), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heA, heS s t f hf g]

end LateralTheory.E.LCIsoPf
end
end

