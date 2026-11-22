import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

def frontCell {n : ℕ} (I : KH.Cell K ι n) : KH.Cell K ι 0 :=
  ⟨fun k => {(I.1 k).min' (I.2.1 k)}, fun _ => Finset.singleton_nonempty _, by simp⟩

def restrict0 {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0) {n : ℕ}
    (I : KH.Cell K ι n) : LocalizedModule (KH.cellMon S I.1) M :=
  KH.cellRes S M (frontCell I).1 I.1 (z (frontCell I))

variable (S ι) in

abbrev KosC (V : Ideal (MRingOver S ι)) (R p n : ℕ) : Type :=
  {J : Finset (Fin R) // J.card = p} → KH.CechC S ι (MRingOver S ι ⧸ V) n

def kosSign {R : ℕ} (J : Finset (Fin R)) (j : Fin R) : ℤ :=
  (-1) ^ (J.filter (· < j)).card

def kosD {V : Ideal (MRingOver S ι)} {R : ℕ} (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) (p n : ℕ) :
    KosC S ι V R (p + 1) n →+ KosC S ι V R p n where
  toFun φ J I := ∑ j : Fin R, if h : j ∈ J.1 then 0 else
    (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
      (restrict0 (z j) I * φ ⟨insert j J.1, by rw [Finset.card_insert_of_notMem h, J.2]⟩ I)
  map_zero' := by
    funext J I
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs
    · rfl
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero (restrict0 (z j) I))).trans (mul_zero _)
  map_add' φ ψ := by
    funext J I
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact (add_zero 0).symm
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_add (restrict0 (z j) I) _ _)).trans (mul_add _ _ _)

variable [LinearOrder K]

variable (S ι) in

def kosCech (V : Ideal (MRingOver S ι)) (R p n : ℕ) : KosC S ι V R p n →+ KosC S ι V R p (n + 1) :=
  (KH.cechD S ι (MRingOver S ι ⧸ V) n).toAddMonoidHom.compLeft _

variable [∀ k, Fintype (ι k)]

variable (S ι) in

def kosPart (V : Ideal (MRingOver S ι)) (R : ℕ) (α c : K → ℤ) (p n : ℕ) : AddSubgroup (KosC S ι V R p n) :=
  (Submodule.pi Set.univ fun _ => KH.cechCc ι (KH.quotPart S V) (c - (p : ℤ) • α) n).toAddSubgroup

end KoszulCech

open KoszulCech

def KoszulCechComplex.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) →
    ∀ (c : K → ℤ) (p n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ ∈ kosPart S ι V R α c p n) ∧
      (∀ φ, kosCech S ι V R p n (kosD z p n φ) = kosD z p (n + 1) (kosCech S ι V R (p + 1) n φ)) ∧
      (∀ φ, kosD z p n (kosD z (p + 1) n φ) = 0)

section Inhabitants

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

def polyCochain (V : Ideal (MRingOver S ι)) (f : MRingOver S ι) : KH.CechC S ι (MRingOver S ι ⧸ V) 0 :=
  fun _ => LocalizedModule.mk (Ideal.Quotient.mk V f) 1

omit [∀ k, Fintype (ι k)] in

theorem cechD_polyCochain (V : Ideal (MRingOver S ι)) (f : MRingOver S ι) :
    KH.cechD S ι (MRingOver S ι ⧸ V) 0 (polyCochain V f) = 0 := by
  classical
  set M := MRingOver S ι ⧸ V
  have hres : ∀ F J : ∀ k, Finset (ι k), (∀ l, F l ⊆ J l) →
      KH.cellRes S M F J (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) =
        LocalizedModule.mk (Ideal.Quotient.mk V f) 1 := by
    intro F J hFJ
    have hle : KH.cellMon S F ≤ KH.cellMon S J := by
      apply Submonoid.closure_mono
      rintro g ⟨k, j, hj, rfl⟩
      exact ⟨k, j, hFJ k hj, rfl⟩
    unfold KH.cellRes
    rw [dif_pos hle, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.liftOfLE_apply,
      LocalizedModule.mkLinearMap_apply]
  funext J
  obtain ⟨J, hJne, hJ⟩ := J
  rw [KH.cechD]
  erw [LinearMap.pi_apply]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hle : (J k).card - 1 ≤ 1 := by
    have : (J k).card - 1 ≤ ∑ l, ((J l).card - 1) :=
      Finset.single_le_sum (f := fun l => (J l).card - 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    omega
  have hpos := (hJne k).card_pos
  have hface : ∀ x ∈ J k, ∀ y ∈ J k,
      ((∀ l, (Function.update J k ((J k).erase x) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase x) l).card - 1) = 0) →
      ((∀ l, (Function.update J k ((J k).erase y) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase y) l).card - 1) = 0) := by
    rintro x hx y hy ⟨h1, h2⟩
    have hcard : ∀ l, (Function.update J k ((J k).erase y) l).card =
        (Function.update J k ((J k).erase x) l).card := by
      intro l
      rcases eq_or_ne l k with rfl | hl
      · simp [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hy]
      · simp [Function.update_of_ne hl]
    refine ⟨fun l => Finset.card_pos.mp ?_, ?_⟩
    · rw [hcard]; exact Finset.card_pos.mpr (h1 l)
    · simp only [hcard]; exact h2
  rcases (show (J k).card = 1 ∨ (J k).card = 2 by omega) with h1 | h2
  · obtain ⟨a, hJk⟩ := Finset.card_eq_one.mp h1
    rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_singleton]
    erw [dif_neg]
    · rfl
    · rintro ⟨hne, -⟩
      have := hne k
      simp [hJk] at this
  · obtain ⟨a, b, hab, hJk⟩ : ∃ a b, a < b ∧ J k = {a, b} := by
      obtain ⟨x, y, hxy, hJk⟩ := Finset.card_eq_two.mp h2
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨x, y, h, hJk⟩
      · exact ⟨y, x, h, by rw [hJk, Finset.pair_comm]⟩
    have ha : a ∈ J k := by rw [hJk]; simp
    have hb : b ∈ J k := by rw [hJk]; simp
    rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_pair hab.ne]
    by_cases hP : (∀ l, (Function.update J k ((J k).erase a) l).Nonempty) ∧
        ∑ l, ((Function.update J k ((J k).erase a) l).card - 1) = 0
    · erw [dif_pos hP, dif_pos (hface a ha b hb hP)]
      change KH.faceSign J k a • KH.cellRes S M (Function.update J k ((J k).erase a)) J
            (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) +
          KH.faceSign J k b • KH.cellRes S M (Function.update J k ((J k).erase b)) J
            (LocalizedModule.mk (Ideal.Quotient.mk V f) 1) = 0
      rw [hres _ _ (fun l => by
            rcases eq_or_ne l k with rfl | hl
            · simp [Finset.erase_subset]
            · simp [Function.update_of_ne hl]),
        hres _ _ (fun l => by
            rcases eq_or_ne l k with rfl | hl
            · simp [Finset.erase_subset]
            · simp [Function.update_of_ne hl])]
      have hsa : KH.faceSign J k a = (-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
        unfold KH.faceSign
        rw [hJk]
        simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
      have hsb : KH.faceSign J k b = -(-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
        unfold KH.faceSign
        rw [hJk]
        simp [Finset.filter_insert, Finset.filter_singleton, hab, pow_succ, pow_add]
      erw [hsa, hsb, neg_smul, add_neg_cancel]
    · have hP' := fun h => hP (hface b hb a ha h)
      erw [dif_neg hP, dif_neg hP']
      simp

end KoszulCech

open KoszulCech

theorem isMultiHomog_one_projectiveLine : IsMultiHomog (1 : MRingOver ℚ (GlobalTheory (Fin 2))) (fun _ => 0) := by
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, GlobalTheory (Fin 2) k) →₀ ℕ)) (a := (1 : ℚ)) hm
  rw [Finset.mem_singleton] at h
  subst h
  simp

theorem isMultiHomog_X_projectiveLine (j : Fin 2) : IsMultiHomog (X ⟨(), j⟩ : MRingOver ℚ (GlobalTheory (Fin 2))) (fun _ => 1) := by
  classical
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := Finsupp.single (⟨(), j⟩ : Σ k, GlobalTheory (Fin 2) k) 1)
    (a := (1 : ℚ)) hm
  rw [Finset.mem_singleton] at h
  subst h
  cases k
  simp [Finsupp.single_apply]

theorem KoszulCechComplex.hyps_inhabited (j : Fin 2) :
    polyCochain (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2)))) (X ⟨(), j⟩) ∈
      KH.cechZc (GlobalTheory (Fin 2)) (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ (GlobalTheory (Fin 2))))) 1 0 := by
  refine ⟨?_, ?_⟩
  · intro J _
    refine Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ (X ⟨(), j⟩), 1, fun _ => 0, isMultiHomog_one_projectiveLine, ?_, rfl⟩
    refine Submodule.subset_span ⟨X ⟨(), j⟩, ⟨fun _ => by norm_num, ?_⟩, rfl⟩
    convert isMultiHomog_X_projectiveLine j using 1
    funext k
    simp
  · show _ ∈ (LinearMap.ker _).restrictScalars ℚ
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact cechD_polyCochain _ _

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockMeasure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N D : ℕ) (v : Fin N → Ω) (B : HermLine (addIdx ι N))
    (J : Ideal (MRing (addIdx ι N))) (R : AnRes (mCoordIdeal (addBlock y v)) J D) [MeasurableSpace R.X]
    [BorelSpace R.X] (dV : Measure R.X),
    IsSmoothHerm A → IsSmoothHerm B → B.a = unitDeg (none : Option K) → IsSmoothVolume R.A dV →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∃ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧
      IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (F : MRing (addIdx ι N)), IsMultiHomog F (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval (addBlock y v) F) =
          Real.sqrt ((1 / 2) *
            ((∫ x, (‖eval (R.lift x x) (map (Int.castRingHom ℂ) F)‖ / B.h (R.lift x x) ^ q) ^ 2 ∂dV) +
              ∫ x, (‖eval (conjPt (R.lift x x)) (map (Int.castRingHom ℂ) F)‖ /
                B.h (conjPt (R.lift x x)) ^ q) ^ 2 ∂dV))

namespace PowerBlockDiag

open ProjLine PowerBlockProjectiveLine

def diagIdx : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → Ix (Fin 2)
  | ⟨none, j⟩ => ⟨(), j⟩
  | ⟨some _, i⟩ => ⟨(), i⟩

def oldIdx (p : Ix (Fin 2)) : Σ k, addIdx (GlobalTheory (Fin 2)) 2 k := ⟨some p.1, p.2⟩

def diagPt (w : Ix (Fin 2) → ℂ) : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ := fun p => w (diagIdx p)

theorem addBlock_apply (p : Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) : addBlock y projectiveLineCoordinates p = y (diagIdx p) := by
  rcases p with ⟨_ | _, i⟩ <;> rfl

theorem rename_diag_mem {f : MRing (addIdx (GlobalTheory (Fin 2)) 2)} (hf : f ∈ mCoordIdeal (addBlock y projectiveLineCoordinates)) :
    rename diagIdx f ∈ mCoordIdeal (ι := GlobalTheory (Fin 2)) y := by
  have key : (mConeMap (ι := GlobalTheory (Fin 2)) y).comp (rename diagIdx) =
      ((rename (fun _ : Option Unit => ())).restrictScalars ℤ).comp (mConeMap (addBlock y projectiveLineCoordinates)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, addBlock_apply]
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at h
  show mConeMap y (rename diagIdx f) = 0
  rw [h]
  have : mConeMap (addBlock y projectiveLineCoordinates) f = 0 := hf
  rw [this, map_zero]

theorem rename_old_mem {f : MRing (GlobalTheory (Fin 2))} (hf : f ∈ mCoordIdeal (ι := GlobalTheory (Fin 2)) y) :
    rename oldIdx f ∈ mCoordIdeal (addBlock y projectiveLineCoordinates) := by
  have key : (mConeMap (addBlock y projectiveLineCoordinates)).comp (rename oldIdx) =
      ((rename (some : Unit → Option Unit)).restrictScalars ℤ).comp (mConeMap (ι := GlobalTheory (Fin 2)) y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldIdx, addBlock]
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at h
  show mConeMap (addBlock y projectiveLineCoordinates) (rename oldIdx f) = 0
  rw [h]
  have : mConeMap (ι := GlobalTheory (Fin 2)) y f = 0 := hf
  rw [this, map_zero]

theorem eval_diagPt (w : Ix (Fin 2) → ℂ) (f : MRing (addIdx (GlobalTheory (Fin 2)) 2)) :
    eval (diagPt w) (map (Int.castRingHom ℂ) f) = eval w (map (Int.castRingHom ℂ) (rename diagIdx f)) := by
  rw [map_rename, eval_rename]
  rfl

theorem eval_oldPart (z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ) (f : MRing (GlobalTheory (Fin 2))) :
    eval (basePart₂ z) (map (Int.castRingHom ℂ) f) = eval z (map (Int.castRingHom ℂ) (rename oldIdx f)) := by
  rw [map_rename, eval_rename]
  rfl

theorem diagPt_mem {w : Ix (Fin 2) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y)) :
    diagPt w ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates)) := by
  obtain ⟨hnz, hvan⟩ := hw
  obtain ⟨i, hi⟩ := hnz ()
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · rcases k with _ | _
    · exact ⟨i, hi⟩
    · exact ⟨i, hi⟩
  · rw [eval_diagPt]
    exact hvan _ (rename_diag_mem hf)

theorem oldPart_mem {z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates))) :
    basePart₂ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) := by
  obtain ⟨hnz, hvan⟩ := hz
  refine ⟨fun _ => hnz (some ()), fun f hf => ?_⟩
  rw [eval_oldPart]
  exact hvan _ (rename_old_mem hf)

theorem graph_pt {z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates))) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ j : Fin 2, z ⟨none, j⟩ = lam * z ⟨some (), j⟩ := by
  obtain ⟨hnz, hvan⟩ := hz
  have hF := hvan _ minor_mem
  simp only [map_sub, map_mul, map_X, eval_X] at hF
  have ha : z ⟨some (), (0 : Fin 2)⟩ ≠ 0 ∨ z ⟨some (), (1 : Fin 2)⟩ ≠ 0 := by
    obtain ⟨i, hi⟩ := hnz (some ())
    change Fin 2 at i
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨lam, h0, h1⟩ : ∃ lam : ℂ, z ⟨none, (0 : Fin 2)⟩ = lam * z ⟨some (), (0 : Fin 2)⟩ ∧
      z ⟨none, (1 : Fin 2)⟩ = lam * z ⟨some (), (1 : Fin 2)⟩ := by
    rcases ha with ha | ha
    · refine ⟨z ⟨none, (0 : Fin 2)⟩ / z ⟨some (), (0 : Fin 2)⟩, by field_simp, ?_⟩
      field_simp
      linear_combination hF
    · refine ⟨z ⟨none, (1 : Fin 2)⟩ / z ⟨some (), (1 : Fin 2)⟩, ?_, by field_simp⟩
      field_simp
      linear_combination -hF
  refine ⟨lam, ?_, fun j => ?_⟩
  · rintro rfl
    obtain ⟨i, hi⟩ := hnz none
    change Fin 2 at i
    fin_cases i
    · exact hi (by simpa using h0)
    · exact hi (by simpa using h1)
  · fin_cases j
    · exact h0
    · exact h1

abbrev JD : Ideal (MRing (addIdx (GlobalTheory (Fin 2)) 2)) := Ideal.span {X ⟨some (), (0 : Fin 2)⟩}

theorem mem_JD_iff (z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ) :
    z ∈ mcPts JD ↔ (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ z ⟨some (), (0 : Fin 2)⟩ = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := h2 _ (Ideal.subset_span rfl)
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [h2]

theorem JD_homog : IsMultiHomogIdeal JD := by
  refine ⟨{(X ⟨some (), (0 : Fin 2)⟩ : MRing (addIdx (GlobalTheory (Fin 2)) 2))}, fun f hf => ?_, rfl⟩
  rw [Set.mem_singleton_iff.mp hf]
  exact ⟨_, isMultiHomog_X _⟩

def liftD (x x' : projectiveLineMultiHomogResolution.X) : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ := diagPt (projectiveLineMultiHomogResolution.lift x x')

theorem liftD_mem (x x' : projectiveLineMultiHomogResolution.X) (hx' : x' ∈ projectiveLineMultiHomogResolution.U x) :
    liftD x x' ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates)) :=
  diagPt_mem (projectiveLineMultiHomogResolution.mem x x' hx')

def resDiag : AnRes (mCoordIdeal (addBlock y projectiveLineCoordinates)) JD 1 where
  homog := JD_homog
  nondeg := by
    intro h
    apply projectiveLineMultiHomogResolution.nondeg
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have := rename_diag_mem (h (Ideal.subset_span rfl))
    simpa [diagIdx, Xc] using this
  X := projectiveLineMultiHomogResolution.X
  A := projectiveLineMultiHomogResolution.A
  U := projectiveLineMultiHomogResolution.U
  isOpen_U := projectiveLineMultiHomogResolution.isOpen_U
  mem_U := projectiveLineMultiHomogResolution.mem_U
  lift := liftD
  holo := fun x p => projectiveLineMultiHomogResolution.holo x (diagIdx p)
  mem := liftD_mem
  compat := fun x x' z hz => by
    obtain ⟨c, hc, h⟩ := projectiveLineMultiHomogResolution.compat x x' z hz
    exact ⟨fun _ => c (), fun _ => hc (), funext fun p => congrFun h (diagIdx p)⟩
  surj := fun z hz hzJ => by
    have ho := oldPart_mem hz
    have hoJ : basePart₂ z ∉ mcPts ProjectiveLineResolution.JJ := fun h =>
      hzJ ((mem_JD_iff z).2 ⟨hz.1, ((ProjectiveLineResolution.mem_J_iff _).1 h).2⟩)
    obtain ⟨x, c, hc, hx⟩ := projectiveLineMultiHomogResolution.surj _ ho hoJ
    obtain ⟨lam, hlam, hnew⟩ := graph_pt hz
    refine ⟨x, fun k => Option.elim k (c () / lam) (fun _ => c ()), ?_, ?_⟩
    · rintro (_ | _)
      · exact div_ne_zero (hc ()) hlam
      · exact hc ()
    · funext p
      rcases p with ⟨_ | _, i⟩
      · change projectiveLineMultiHomogResolution.lift x x ⟨(), i⟩ = c () / lam * z ⟨none, i⟩
        rw [hx, hnew i]
        field_simp
        rfl
      · change projectiveLineMultiHomogResolution.lift x x ⟨(), i⟩ = c () * z ⟨some (), i⟩
        rw [hx]
        rfl
  inj := fun x x' hx h => by
    apply projectiveLineMultiHomogResolution.inj x x'
    · intro hJ
      exact hx ((mem_JD_iff _).2 ⟨(liftD_mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, ((ProjectiveLineResolution.mem_J_iff _).1 hJ).2⟩)
    · obtain ⟨c, hc, hcx⟩ := h
      exact ⟨fun _ => c (some ()), fun _ => hc _, funext fun p => congrFun hcx (oldIdx p)⟩
  null := fun j => by
    have hset : {x | liftD x x ∈ mcPts JD} = {x | projectiveLineMultiHomogResolution.lift x x ∈ mcPts ProjectiveLineResolution.JJ} := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_JD_iff, ProjectiveLineResolution.mem_J_iff]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨(projectiveLineMultiHomogResolution.mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, h⟩
      · rintro ⟨-, h⟩
        exact ⟨(liftD_mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, h⟩
    rw [hset]
    exact projectiveLineMultiHomogResolution.null j

end PowerBlockDiag

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelChartPoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    ∀ σ ∈ Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩),
      ∃ N : ℕ, σ * (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelOneStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelOneStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

