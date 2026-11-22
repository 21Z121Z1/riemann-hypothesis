import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SchCls

theorem sum_neg_one_pow (p : ℕ) : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) = if Even p then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction p with
  | zero => simp [Finset.sum_range_succ]
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd q with h | h
    · have h2 : Even (q + 1 + 1) := by rw [add_assoc]; exact h.add even_two
      simp [h, Nat.even_add_one, h2.neg_one_pow]
    · have h2 : Odd (q + 1 + 1) := by rw [add_assoc]; exact h.add_even even_two
      have h3 : Even (q + 1) := h.add_one
      simp [h3, h2.neg_one_pow, Nat.not_even_iff_odd.mpr h]

variable {R : Type} [CommRing R]

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) : x.face i = x := rfl

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res]

theorem map_id' {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.map (𝟙 F) y = y := rfl

theorem map_units_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (y : Sec F U) :
    Sec.map φ (u • y) = u • Sec.map φ y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem res_units_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (y : Sec F U) :
    Sec.res g (u • y) = u • Sec.res g y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem ev_δ_sch {X : Scheme.{0}} {I : Cx R} {n k : ℤ} (hk : n + 1 = k)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + k = t) (x : Sx (sch.obj X) (p + 1) U) :
    ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      (if Even p then 0 else k.negOnePow • ev α p t (by omega) U x) := by
  rw [CupSpec.ev_δ_succ hk α U p s t hs ht x]
  simp only [face_sch]
  rw [← Finset.sum_smul, sum_neg_one_pow]
  split_ifs <;> simp

end GlobalTheory.EtC.SchCls

namespace GlobalTheory.EtC

open GlobalTheory.EtC.SchCls in

theorem sch_cls_cocycle_sec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := CupSpec.ev_exists (R := R) (E := sch.obj X) (I := I) (n := n)
      (fun p s h U x => if hp : p = 0 then
        Sec.map (I.XIsoOfEq (show n = s by omega)).hom (Sec.res (x : U ⟶ X) z) else 0)
      (by
        intro p s h V U g x
        by_cases hp : p = 0
        · subst hp
          simp only [dif_pos]
          erw [CupSpec.map_res, res_comp]
          rfl
        · simp only [dif_neg hp]
          exact map_zero _)
    have hc : δ n k a = 0 := by
      refine CupSpec.ev_ext _ _ fun p t ht U x => ?_
      erw [CupSpec.ev_zero]
      cases p with
      | zero =>
        have hkt : k = t := by omega
        subst hkt
        erw [CupSpec.ev_δ_zero hnk a U n k (by simp) ht x, ha]
        simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
        erw [← CupSpec.map_res, hz]
        exact map_zero _
      | succ p =>
        erw [ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev a 0 n _ U x = _
      erw [ha]
      simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
    · change ev a (p + 1) s h U x = 0
      erw [ha]
      simp
  · have hδ := Cocycle.δ_eq_zero α k
    refine ⟨?_, ?_⟩
    · have h0 := CupSpec.ev_δ_zero hnk α.1 X n k (by simp) (by simp) (𝟙 X)
      erw [hδ, CupSpec.ev_zero] at h0
      exact h0.symm
    erw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, CupSpec.ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := CupSpec.ev_exists (R := R) (E := sch.obj X) (I := I) (n := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev α.1 (p + 1) s (by omega) U x)
        (by
          intro p s h V U g x
          by_cases hp : p = 0
          · subst hp
            simp only [dif_pos]
            erw [CupSpec.map_res, res_comp]
            rfl
          · simp only [dif_neg hp]
            split_ifs
            · exact map_zero _
            · erw [res_units_smul, CupSpec.ev_res]
              rfl)
      refine ⟨b, CupSpec.ev_ext _ _ fun p t ht U x => ?_⟩
      cases p with
      | zero =>
        have hnt : n = t := by omega
        subst hnt
        erw [CupSpec.ev_δ_zero hmn b U m n (by simp) ht x, hb]
        simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
        erw [← CupSpec.map_res, hy, CupSpec.ev_res]
        congr 1
      | succ p =>
        erw [ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
        erw [hδ, CupSpec.ev_zero] at hc
        rcases Nat.even_or_odd p with he | ho
        · have hne : ¬ Even (p + 1) := Nat.not_even_iff_odd.mpr he.add_one
          simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, hne, if_false, if_pos he,
            add_zero] at hc ⊢
          erw [map_units_smul, eq_neg_of_add_eq_zero_left hc.symm, smul_neg, smul_smul]
          simp [Int.units_mul_self]
        · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr ho
          have hp0 : p ≠ 0 := fun h => hne (h ▸ (⟨0, rfl⟩ : Even 0))
          have hev : Even (p + 1) := ho.add_one
          simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, hev, if_true, hne, if_false,
            dif_neg hp0, map_zero, zero_add]
          have hkn : k.negOnePow = -n.negOnePow := by rw [← hnk, Int.negOnePow_succ]
          erw [hkn, neg_neg, smul_smul, Int.units_mul_self, one_smul]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2Bound
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_pow_mul_iteratedFDeriv_le_sqrt_sum_weighted_sq :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ k n
  obtain hd | ⟨m, hm⟩ : finrank ℝ E = 0 ∨ ∃ m, finrank ℝ E = m + 1 := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨finrank ℝ E - 1, by omega⟩
  · exact GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero μ hd k n
  obtain ⟨C5, hC5, h5⟩ := GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv μ m hm
  obtain ⟨C6, hC6, h6⟩ := GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)) μ
  refine ⟨max (n + (m + 1)) (k + finrank ℝ E + 1), (C5 * C6).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f x
  set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ := iteratedFDeriv ℝ n f with hGdef
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := (f.smooth ⊤).iteratedFDeriv_right (by
    first
    | (rw [← WithTop.coe_natCast, ← WithTop.coe_add, top_add])
    | exact le_of_eq (by simp)
    | (norm_cast))
  have hdec : ∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0) := by
    intro j _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := tendsto_zero_iff_norm_tendsto_zero.1 (GlobalTheory.T.schwartz_iteratedFDeriv_tendsto_zero_cocompact' f (n + j))
    simpa [G, GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv'] using this
  have hcont : Continuous (iteratedFDeriv ℝ (m + 1) G) :=
    hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hn : ∀ z, ‖iteratedFDeriv ℝ (m + 1) G z‖ = ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖ :=
    fun z => GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' _ _ _ z
  have e1 := h5 G hG hdec k x
  have e2 := h6 _ hcont k
  simp only [hn] at e1 e2
  set a := ∫ z, (‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  set b := ∫ z, (‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2 ∂μ
  have ha : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal a :=
    (ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have hb : ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖iteratedFDeriv ℝ (n + (m + 1)) f z‖) ^ 2) ∂μ
      = ENNReal.ofReal b :=
    (ofReal_integral_eq_lintegral_ofReal (GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz μ f _ _) (Eventually.of_forall fun z => sq_nonneg _)).symm
  have ha0 : 0 ≤ a := integral_nonneg fun z => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun z => sq_nonneg _
  rw [ha, hb, ← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at e2
  have e3 : ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C5 * C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ)) := by
    calc _ ≤ _ := e1
      _ ≤ C5 * (C6 * ENNReal.ofReal ((a + b) ^ (1 / 2 : ℝ))) := by gcongr
      _ = _ := (mul_assoc _ _ _).symm
  have e4 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC5 hC6) ENNReal.ofReal_ne_top) e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ← Real.sqrt_eq_rpow] at e4
  refine e4.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) ENNReal.toReal_nonneg)

  set T : ℕ → ℕ → ℝ := fun i j => ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ
  have hT : ∀ i j, 0 ≤ T i j := fun i j => integral_nonneg fun z => sq_nonneg _
  set N := max (n + (m + 1)) (k + finrank ℝ E + 1)
  have hj : n + (m + 1) ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hrow : ∀ i, T i (n + (m + 1)) ≤ ∑ j ∈ Finset.range (N + 1), T i j := fun i =>
    Finset.single_le_sum (fun j _ => hT i j) hj
  calc a + b = T k (n + (m + 1)) + T (k + finrank ℝ E + 1) (n + (m + 1)) := rfl
    _ ≤ (∑ j ∈ Finset.range (N + 1), T k j) + ∑ j ∈ Finset.range (N + 1), T (k + finrank ℝ E + 1) j :=
        add_le_add (hrow _) (hrow _)
    _ ≤ ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), T i j :=
        Finset.add_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hT i j)
          (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 (by omega)) (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

def unitsT : CommRingCat.{0} ⥤ Type where
  obj A := (A : Type)ˣ
  map {A B} f := TypeCat.ofHom fun (u : (A : Type)ˣ) => Units.map f.hom.toMonoidHom u
  map_id A := by ext u; rfl
  map_comp f g := by ext u; rfl

structure Trip (q : ℕ) (A : Type) [CommRing A] where
  root : Prim q A
  src : Aˣ
  tgt : Aˣ
  tgt_eq : (tgt : A) = root.1 * src

def Trip.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Trip q A) : Trip q B :=
  ⟨x.root.map f, Units.map f.toMonoidHom x.src, Units.map f.toMonoidHom x.tgt, by
    change f (x.tgt : A) = f x.root.1 * f (x.src : A)
    rw [x.tgt_eq, map_mul]⟩

def tripT (q : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Trip q A
  map f := TypeCat.ofHom (Trip.map f.hom)
  map_id A := by
    ext x
    cases x
    rfl
  map_comp f g := by
    ext x
    cases x
    rfl

def unitsP : PSh := Scheme.Γ ⋙ unitsT

def tripP (q : ℕ) : PSh := Scheme.Γ ⋙ tripT q

def unitsP.mk {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) : unitsP.obj (op U) := v

def tripP.mk {q : ℕ} {U : Scheme.{0}} (x : Trip q Γ(U, ⊤)) : (tripP q).obj (op U) := x

def tripP.get {q : ℕ} {U : Scheme.{0}} (x : (tripP q).obj (op U)) : Trip q Γ(U, ⊤) := x

theorem unitsP.map_mk {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ) :
    unitsP.map g.op (unitsP.mk v) = unitsP.mk (Units.map g.appTop.hom.toMonoidHom v) := rfl

theorem tripP.get_map {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : (tripP q).obj (op U)) :
    tripP.get ((tripP q).map g.op x) = (tripP.get x).map g.appTop.hom := rfl

theorem smap_sum {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.map φ (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.map φ (f x) := by
  simp only [Sec.map, map_finsuppSum, map_smul]

theorem res_sum {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.res g (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.res g (f x) := by
  simp only [Sec.res, map_finsuppSum, map_smul]

theorem smap_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_eq_zero_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (s : Sec F U)
    (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  obtain ⟨S, hS, hS'⟩ := h
  exact Sheaf.isSeparated F U S hS s 0 (fun V g hg => (hS' V g hg).trans (map_zero _).symm)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U)) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

end GlobalTheory.EtC.KummerSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSlice
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem eq_of_isFirstMax_of_isFirstMax {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by
  apply idx.injective
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (not_lt.2 (h.2 J').1)
  · exact he
  · exact absurd ((h.2 J').2 hl) (not_lt.2 (h'.2 J).1)

theorem sec_inv_mul_mem_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  intro k _ _ _ _ a d Y J hJ
  have hex : ∃ J, IsFirstMax Y J := ⟨J, hJ⟩
  have hc : hex.choose = J := eq_of_isFirstMax_of_isFirstMax hex.choose_spec hJ
  have hs : (sec Y).val = Y.submatrix id J := by
    unfold sec
    rw [dif_pos hex]
    show Y.submatrix id hex.choose = _
    rw [hc]
  have hsub : (((sec Y)⁻¹).val * Y).submatrix id J = ((sec Y)⁻¹).val * Y.submatrix id J := by
    ext i j; simp [Matrix.mul_apply]
  have hdet : (((sec Y)⁻¹).val).det = (minor Y J)⁻¹ := by
    have e := congrArg Matrix.det (sec Y).inv_mul
    rw [Matrix.det_mul, Matrix.det_one, hs] at e
    exact eq_inv_of_mul_eq_one_left e
  refine ⟨J, ?_, fun J' => ?_⟩
  · rw [hsub, ← hs]; exact (sec Y).inv_mul
  · rw [minor_mul, hdet, map_mul, map_inv₀]
    have h0 : valuation k (minor Y J) ≠ 0 := by simpa using hJ.1
    constructor
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').1
    · intro hl
      rw [inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').2 hl

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ClsBasic

variable {R : Type} [CommRing R]

theorem single_add' {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q : ℤ}
    (f g : K.X p ⟶ L.X q) (n : ℤ) : Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem ofHom_comp_single {C : Type*} [Category C] [Preadditive C] {K K' L : CochainComplex C ℤ} {p q : ℤ}
    (g : K' ⟶ K) (f : K.X p ⟶ L.X q) (n : ℤ) :
    (Cochain.ofHom g).comp (Cochain.single f n) (zero_add n) = Cochain.single (g.f p ≫ f) n := by
  ext p' q' h
  rw [Cochain.comp_v _ _ (zero_add n) p' p' q' (add_zero p') h, Cochain.ofHom_v]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h0 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h0, zero_comp] at h
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0) ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  erw [Category.assoc, h]
  all_goals first | rfl | exact comp_zero

theorem chains_d (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := n + 1) (j := n) rfl rfl
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  rw [← h2]
  exact h

theorem chainsXIso_nat {E E' : Spc} (f : E' ⟶ E) (n : ℕ) :
    ((chains R).map f).f (-(n : ℤ)) ≫ (chainsXIso R E n).hom = (chainsXIso R E' n).hom ≫ (free R).map (f.app (op ⦋n⦌)) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  rw [h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem δ_cls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
      (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
        ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
  rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
  rw [Category.assoc, Category.assoc, resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
  congr 2
  rw [chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [cobd, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp]

end GlobalTheory.EtC.ClsBasic

open GlobalTheory.EtC.ClsBasic in

theorem GlobalTheory.EtC.isCls_basic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧ (∀ (s s' : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧ (∀ (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s x' → x = x') ∧ (∀ (t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)), IsCls (cobd t) x → x = 0) ∧ ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n), IsCls s x → IsCls ((free R).map (f.app (op ⦋n⦌)) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_, fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [δ_cls, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, δ_cls, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ofHom_comp_single, ← Category.assoc, chainsXIso_nat]
    simp only [Category.assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberField
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

noncomputable section

namespace GlobalTheory.QSA

theorem sqOpen_and_nhdsNE_zero_neBot_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')
  refine ⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩
  infer_instance

end GlobalTheory.QSA

end
end

