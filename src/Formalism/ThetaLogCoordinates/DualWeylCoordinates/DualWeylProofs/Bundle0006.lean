import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0005
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0004
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsRemIffAdd
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0002

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ClosureBasicModules
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem closure_first_part_of : LemmaA → SBasis → ClosureBasicModules := by
  intro hA hS n _
  refine ⟨fun M h1 h => qc_colFam_triv M h1 h, fun M mu β hmu hβ => qc_colFam_SMu hA hS hmu hβ, ?_⟩
  rintro M M' ε _ e h ⟨CF⟩
  exact qc_colFam_tw M M' ε e h CF

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestWeightIntegral
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_lastIdx (m : ℕ) : lastIdx (m + 1) = Fin.last m := rfl

section Cols

variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_colH_le (hi : Interl lam nu) (c : ℤ) : colH nu c ≤ colH lam c := by
  unfold colH
  rw [← Finset.card_map Fin.castSuccEmb]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha.trans (hi a).1

lemma qr_colH_le' (hi : Interl lam nu) (c : ℤ) : colH lam c ≤ colH nu c + 1 := by
  unfold colH
  rw [← Finset.card_map (Fin.succEmb m)]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le (0 : Fin (m + 1)) _)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  induction x using Fin.cases with
  | zero => left; rfl
  | succ a => right; exact ⟨a, hx.trans (hi a).2, rfl⟩

lemma qr_colH_eq (hi : Interl lam nu) (c : ℤ) :
    colH lam c = colH nu c + if colH lam c = colH nu c + 1 then 1 else 0 := by
  have h1 := qr_colH_le hi c
  have h2 := qr_colH_le' hi c
  split_ifs with h <;> omega

lemma qr_sum_colH {n : ℕ} (mu : Fin n → ℤ) (L U : ℤ) (h : ∀ a, L ≤ mu a ∧ mu a ≤ U) :
    ∑ c ∈ Finset.Ioc L U, (colH mu c : ℤ) = ∑ a, (mu a - L) := by
  have h1 : ∀ c, (colH mu c : ℤ) = ∑ a, if c ≤ mu a then 1 else 0 := by
    intro c
    rw [colH, Finset.card_filter]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (Finset.Ioc L U).filter (fun c => c ≤ mu a) = Finset.Ioc L (mu a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have := (h a).2
    constructor
    · rintro ⟨⟨h3, _⟩, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h3, h4⟩; exact ⟨⟨h3, h4.trans this⟩, h4⟩
  rw [h2, Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.2 (h a).1)]

end Cols

section J

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_le_last (hn : Dominant nu) (a : Fin m) : nu (lastIdx m) ≤ nu a := by
  apply hn
  rw [Fin.le_def]
  show a.1 ≤ m - 1
  have := a.2
  omega

lemma qr_le_zero {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hn : Dominant mu) (a : Fin n) : mu a ≤ mu 0 := hn (Fin.zero_le a)

lemma qr_lam_last_le (hi : Interl lam nu) : lam (Fin.last m) ≤ nu (lastIdx m) := by
  have h := (hi (lastIdx m)).2
  have h1 : (lastIdx m).succ = Fin.last m := by
    apply Fin.ext
    show m - 1 + 1 = m
    have := NeZero.pos m
    omega
  rwa [h1] at h

lemma qr_nu_zero_le (hi : Interl lam nu) : nu 0 ≤ lam 0 := (hi 0).1

lemma qr_TCols_sub (hi : Interl lam nu) {c : ℤ} (hc : c ∈ TCols nu) : c ∈ TCols lam := by
  simp only [TCols, Finset.mem_Ioc, qr_lastIdx] at hc ⊢
  exact ⟨lt_of_le_of_lt (qr_lam_last_le hi) hc.1, hc.2.trans (qr_nu_zero_le hi)⟩

lemma qr_colH_low (hn : Dominant nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) : colH nu c = m := by
  rw [colH, Finset.filter_true_of_mem]
  · simp
  · intro a _; exact hc.trans (qr_le_last hn a)

lemma qr_colH_high (hn : Dominant nu) {c : ℤ} (hc : nu 0 < c) : colH nu c = 0 := by
  rw [colH, Finset.filter_false_of_mem]
  · simp
  · intro a _; exact not_le.2 (lt_of_le_of_lt (qr_le_zero hn a) hc)

lemma qr_subsing (hn : Dominant nu) {c : ℤ} (hc : c ∉ TCols nu) :
    Subsingleton {S : Finset (Fin m) // S.card = colH nu c} := by
  simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  constructor
  rintro ⟨S, hS⟩ ⟨S', hS'⟩
  apply Subtype.ext
  show S = S'
  rcases hc with hc | hc
  · rw [qr_colH_low hn hc] at hS hS'
    rw [Finset.eq_univ_of_card S (by simpa using hS), Finset.eq_univ_of_card S' (by simpa using hS')]
  · rw [qr_colH_high hn hc] at hS hS'
    rw [Finset.card_eq_zero.1 hS, Finset.card_eq_zero.1 hS']

def qr_can (nu : Fin m → ℤ) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  ⟨(univ : Finset (Fin (colH nu c))).map (Fin.castLEEmb (colH_le nu c)), by simp⟩

def qr_base (I' : TIdx nu) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  if h : c ∈ TCols nu then I' ⟨c, h⟩ else qr_can nu c

lemma qr_base_can (c : ℤ) : qr_base (canT nu) c = qr_can nu c := by
  unfold qr_base
  split_ifs <;> rfl

lemma qr_base_mem (I' : TIdx nu) (c : ↥(TCols nu)) : qr_base I' c = I' c := by
  unfold qr_base
  rw [dif_pos c.2]

def qr_j (hi : Interl lam nu) (I' : TIdx nu) : TIdx lam := fun c =>
  ⟨qr_ext (colH lam c = colH nu c + 1) (qr_base I' c).1, by
    rw [qr_ext_card, (qr_base I' c).2]; exact (qr_colH_eq hi c).symm⟩

lemma qr_j_inj (hi : Interl lam nu) : Function.Injective (qr_j (lam := lam) hi) := by
  intro I' K' h
  funext c
  have h1 := congrArg Subtype.val (congrFun h ⟨c.1, qr_TCols_sub hi c.2⟩)
  have h2 := qr_ext_inj _ h1
  rw [qr_base_mem, qr_base_mem] at h2
  exact Subtype.ext h2

lemma qr_j_surj (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam)
    (hK : ∀ c : ↥(TCols lam), (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1)) :
    ∃ K' : TIdx nu, qr_j hi K' = K := by
  have hc : ∀ c : ↥(TCols lam), (univ.filter fun a : Fin m => a.castSucc ∈ (K c).1).card = colH nu c := by
    intro c
    have h1 := congrArg Finset.card (qr_ext_surj _ (K c).1 (hK c))
    rw [qr_ext_card, (K c).2] at h1
    have h2 := qr_colH_eq hi c
    omega
  refine ⟨fun c => ⟨_, hc ⟨c.1, qr_TCols_sub hi c.2⟩⟩, ?_⟩
  funext c
  apply Subtype.ext
  show qr_ext _ _ = _
  rw [qr_ext_surj _ (K c).1 (hK c)]
  congr 1
  by_cases h : c.1 ∈ TCols nu
  · rw [qr_base, dif_pos h]
  · have := qr_subsing hn h
    exact congrArg Subtype.val (Subsingleton.elim (qr_base _ c.1) ⟨_, hc c⟩)

lemma qr_can_sub (c : ℤ) : (qr_can nu (c + 1)).1 ⊆ (qr_can nu c).1 := by
  intro x hx
  simp only [qr_can, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le nu c)⟩, rfl⟩

lemma qr_j_can_std (hi : Interl lam nu) : StdT (qr_j (lam := lam) hi (canT nu)) := by
  intro c hc t
  show ((qr_ext _ (qr_base (canT nu) (c.1 + 1)).1).filter (· ≤ t)).card ≤
    ((qr_ext _ (qr_base (canT nu) c.1).1).filter (· ≤ t)).card
  rw [qr_base_can, qr_base_can]
  induction t using Fin.lastCases with
  | last =>
    rw [qr_filter_last, qr_filter_last, qr_ext_card, qr_ext_card, (qr_can nu _).2, (qr_can nu _).2,
      ← qr_colH_eq hi, ← qr_colH_eq hi]
    exact qc_colH_succ_le lam c
  | cast t =>
    rw [qr_filter_castSucc, qr_filter_castSucc, Finset.card_map, Finset.card_map]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (qr_can_sub c.1))

end J

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_card_Idx {M : GLMod n} (CF : ColFam M) : Fintype.card (qb_Idx CF) = Fintype.card M.ι := by
  rw [Fintype.card_sigma, CF.rank]
  refine sum_congr rfl fun j _ => ?_
  rw [dMu, Nat.card_eq_fintype_card]

def qb_e {M : GLMod n} (CF : ColFam M) : M.ι ≃ qb_Idx CF := Fintype.equivOfCardEq (qb_card_Idx CF).symm

def qb_N {M : GLMod n} (CF : ColFam M) : Matrix M.ι M.ι ℤ :=
  Matrix.of fun k i => CF.vec (qb_e CF k).1 (qb_e CF k).2.1 i

lemma qb_N_row {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    ((qb_N CF).map (Int.castRingHom R)).row = qb_vecF CF R ∘ qb_e CF := rfl

theorem qb_N_det (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : IsUnit (qb_N CF).det := by
  rw [Int.isUnit_iff_natAbs_eq, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  haveI := Fact.mk hp
  have h1 : LinearIndependent (ZMod p) ((qb_N CF).map (Int.castRingHom (ZMod p))).row := by
    rw [qb_N_row]; exact (linearIndependent_equiv (qb_e CF)).2 (qb_indep_field hA CF (ZMod p))
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h1
  have h2 : ((qb_N CF).map (Int.castRingHom (ZMod p))).det = ((qb_N CF).det : ZMod p) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [h2] at h1
  apply h1.ne_zero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.2 hdvd

theorem qb_N_unit (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    IsUnit ((qb_N CF).map (Int.castRingHom R)) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (qb_N_det hA CF).map _

theorem qb_basisR (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    LinearIndependent R (qb_vecF CF R) ∧ Submodule.span R (Set.range (qb_vecF CF R)) = ⊤ := by
  have hu := qb_N_unit hA CF R
  constructor
  · have := Matrix.linearIndependent_rows_of_isUnit hu
    rw [qb_N_row] at this
    exact (linearIndependent_equiv (qb_e CF)).1 this
  · have h1 := Matrix.vecMul_surjective_iff_isUnit.2 hu
    have h2 := _root_.range_vecMulLinear ((qb_N CF).map (Int.castRingHom R))
    rw [qb_N_row, EquivLike.range_comp] at h2
    rw [← h2, LinearMap.range_eq_top]
    exact h1

def qb_basis (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    Module.Basis (qb_Idx CF) R (M.ι → R) :=
  Module.Basis.mk (qb_basisR hA CF R).1 (qb_basisR hA CF R).2.ge

lemma qb_basis_apply (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : qb_Idx CF) :
    qb_basis hA CF R x = qb_vecF CF R x := by
  rw [qb_basis, Module.Basis.mk_apply]

lemma qb_vecF_int {M : GLMod n} (CF : ColFam M) : qb_vecF CF ℤ = fun x => CF.vec x.1 x.2.1 := by
  funext x i
  simp [qb_vecF]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qs_ext (mu : Fin n → ℤ) (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅

lemma qs_ext_mem (mu : Fin n → ℤ) (I : TIdx mu) (c : ↥(TCols mu)) : qs_ext mu I c.1 = (I c).1 := by
  simp [qs_ext, c.2]

lemma qs_colH_low {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) : colH mu c = n := by
  unfold colH
  rw [Finset.filter_true_of_mem (fun m _ => hc.trans (hmu (qb_le_lastIdx m)))]; simp

lemma qs_colH_high {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) : colH mu c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem (fun m _ => by have := hmu (Fin.zero_le m); omega)]; simp

lemma qs_ext_card {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (c : ℤ) :
    (qs_ext mu I c).card = colH mu c := by
  unfold qs_ext
  split_ifs with h1 h2
  · exact (I ⟨c, h1⟩).2
  · rw [qs_colH_low hmu h2]; simp
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp

def qs_res (mu : Fin n → ℤ) (F : ℤ → Finset (Fin n)) (hF : ∀ c, (F c).card = colH mu c) : TIdx mu :=
  fun c => ⟨F c.1, hF c.1⟩

lemma qs_ext_res {mu : Fin n → ℤ} (hmu : Dominant mu) (F : ℤ → Finset (Fin n))
    (hF : ∀ c, (F c).card = colH mu c) : qs_ext mu (qs_res mu F hF) = F := by
  funext c
  unfold qs_ext
  split_ifs with h1 h2
  · rfl
  · symm; apply Finset.eq_univ_of_card; rw [hF, qs_colH_low hmu h2]; simp
  · symm; rw [← Finset.card_eq_zero, hF, qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]

lemma qs_ext_inj (mu : Fin n → ℤ) : Function.Injective (qs_ext mu) := by
  intro I I' h
  funext c
  apply Subtype.ext
  rw [← qs_ext_mem, ← qs_ext_mem, h]

lemma qs_collapse {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) (P : Prop) [Decidable P]
    (F : ℤ → Finset (Fin n)) (hF : P → ∀ c, (F c).card = colH mu c) (f : (ℤ → Finset (Fin n)) → M)
    [∀ I : TIdx mu, Decidable (P ∧ qs_ext mu I = F)] :
    ∑ I : TIdx mu, (if P ∧ qs_ext mu I = F then f (qs_ext mu I) else 0) = if P then f F else 0 := by
  classical
  split_ifs with hP
  · rw [Finset.sum_eq_single (qs_res mu F (hF hP))]
    · rw [if_pos ⟨hP, qs_ext_res hmu F (hF hP)⟩, qs_ext_res hmu]
    · intro I _ hI
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hI (qs_ext_inj mu (by rw [h, qs_ext_res hmu]))
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun I _ => if_neg fun h => hP h.1

def qs_ini (h : ℕ) : Finset (Fin n) := univ.filter fun x => x.1 < h

lemma qs_ext_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) : qs_ext mu (canT mu) c = qs_ini (colH mu c) := by
  unfold qs_ext
  split_ifs with h1 h2
  · ext b; rw [qb_mem_canT]; simp [qs_ini]
  · rw [qs_colH_low hmu h2]; ext b; simp [qs_ini]
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp [qs_ini]

omit [NeZero n] in
lemma qs_minorC_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    minorC J I hJ hI = qs_mn (qs_gC n) J I := by
  rw [qs_mn_eq _ J I hJ hI, minorC, RingHom.map_det]
  rfl

omit [NeZero n] in
lemma qs_mn_univ : qs_mn (qs_gC n) univ univ = ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) := by
  have hc : (univ : Finset (Fin n)).card = n := by simp
  rw [qs_mn_eq _ _ _ hc hc]
  have h1 : ∀ a, (univ : Finset (Fin n)).orderEmbOfFin hc a = a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique hc (f := id) (fun _ => mem_univ _) strictMono_id) a).symm
  simp only [h1]
  show _ = algebraMap _ _ (genMat ℤ n).det
  rw [RingHom.map_det]; rfl

omit [NeZero n] in
lemma qs_mn_empty {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) : qs_mn g ∅ ∅ = 1 := by
  rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp

def qs_TM (lo : ℤ) (S : Finset ℤ) (J I : ℤ → Finset (Fin n)) : GLCoord ℤ n :=
  ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * ∏ c ∈ S, qs_mn (qs_gC n) (J c) (I c)

theorem qs_TMat_eq {mu : Fin n → ℤ} (hmu : Dominant mu) (lo hi : ℤ) (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ hi)
    (J I : TIdx mu) : TMat mu J I = qs_TM lo (Finset.Ioc lo hi) (qs_ext mu J) (qs_ext mu I) := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have hS : Finset.Ioc lo hi = Finset.Ioc lo (mu (lastIdx n)) ∪ (TCols mu ∪ Finset.Ioc (mu 0) hi) := by
    rw [TCols, Finset.Ioc_union_Ioc_eq_Ioc h0 h2, Finset.Ioc_union_Ioc_eq_Ioc h1 (h0.trans h2)]
  have hA : ∏ c ∈ Finset.Ioc lo (mu (lastIdx n)), qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) ^ (mu (lastIdx n) - lo).toNat := by
    rw [← Int.card_Ioc, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hc2 : c ≤ mu (lastIdx n) := (Finset.mem_Ioc.1 hc).2
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    simp only [qs_ext, dif_neg hc1, if_pos hc2, qs_mn_univ]
  have hB : ∏ c ∈ TCols mu, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2 := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [qs_ext_mem, qs_ext_mem, qs_minorC_eq]
  have hC : ∏ c ∈ Finset.Ioc (mu 0) hi, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hc2 : mu 0 < c := (Finset.mem_Ioc.1 hc).1
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    have hc3 : ¬ c ≤ mu (lastIdx n) := by omega
    simp only [qs_ext, dif_neg hc1, if_neg hc3, qs_mn_empty]
  have hU : detU n ^ mu (lastIdx n) = detU n ^ lo * detU n ^ (mu (lastIdx n) - lo).toNat := by
    rw [← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (by omega)]; congr 1; omega
  rw [qs_TM, hS, Finset.prod_union, Finset.prod_union, hA, hB, hC, TMat, hU, Units.val_mul, Units.val_pow_eq_pow_val]
  · ring
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc] at hx hx'; omega
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc, mem_union] at hx hx'; omega

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QxPhApply
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}

lemma qx_ps_equiv (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) :
    ∑ y : TIdx mu × κ, TMat mu K y.1 * B k y.2 * (ps mu nu y I : GLCoord ℤ n) =
      ∑ I', (ps mu nu (K, k) I' : GLCoord ℤ n) * TMat nu I' I :=
  congrFun (congrFun (hd.2.2.2.1 mu hmu nu hnu) (K, k)) I

lemma qx_wt (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) (h : ps mu nu (K, k) I ≠ 0) :
    qb_wtT mu K + be k = qb_wtT nu I := by
  have h1 := congrArg (evGL (torusPt n)) (qx_ps_equiv hd hmu hnu K k I)
  simp only [map_sum, map_mul, map_intCast, qb_evGL_torus_TMat, hd.2.1, Fintype.sum_prod_type,
    ite_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true,
    AddMonoidAlgebra.single_mul_single, one_mul] at h1
  by_contra hne
  have h2 := congrArg (fun x => x.coeff (qb_wtT nu I)) h1
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, if_neg hne, if_true, mul_zero, mul_one] at h2
  exact h h2.symm

lemma qx_wt_can (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (h : ps mu nu (K, k) (canT nu) ≠ 0) : qb_wtT mu K = nu - be k := by
  have h1 := qx_wt hd hmu hnu K k _ h
  rw [qb_wtT_can (hd.2.2.1 mu hmu nu hnu)] at h1
  rw [← h1, add_sub_cancel_right]

variable {M M' : GLMod n}

abbrev qx_J (Str : (Fin n → ℤ) → Finset (Fin n → ℤ)) (CF : ColFam M) : Type :=
  Σ j : CF.J, ↥(Str (CF.mu j))

def qx_ph (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M)
    (x : qx_J Str CF) : Matrix M'.ι (TIdx (x.2 : Fin n → ℤ)) ℤ :=
  fun i I => ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I

lemma qx_ph_apply (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (x : qx_J Str CF) (i : M'.ι)
    (I : TIdx (x.2 : Fin n → ℤ)) :
    qx_ph ps e CF x i I = ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I := rfl

lemma qx_equiv (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M)
    (x : qx_J Str CF) (i : M'.ι) (I : TIdx (x.2 : Fin n → ℤ)) :
    ∑ k, M'.A i k * (qx_ph ps e CF x k I : GLCoord ℤ n) =
      ∑ I', (qx_ph ps e CF x i I' : GLCoord ℤ n) * TMat (x.2 : Fin n → ℤ) I' I := by
  obtain ⟨j, nu, hnu⟩ := x
  have hmu := CF.dom j
  have hT' : ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2 := hT
  simp only [qx_ph_apply, hT', Int.cast_sum, Int.cast_mul]
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  calc ∑ m, ∑ k, M.A (e i).1 m * B (e i).2 k *
        ∑ K, (CF.ph j m K : GLCoord ℤ n) * (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)
      = ∑ K, ∑ k, (∑ m, M.A (e i).1 m * (CF.ph j m K : GLCoord ℤ n)) * (B (e i).2 k *
          (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)) := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        refine sum_congr rfl fun K _ => sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    _ = ∑ K', (CF.ph j (e i).1 K' : GLCoord ℤ n) * ∑ y : TIdx (CF.mu j) × κ,
          TMat (CF.mu j) K' y.1 * B (e i).2 y.2 * (ps (CF.mu j) nu y I : GLCoord ℤ n) := by
        simp only [qb_equiv_apply, Fintype.sum_prod_type, mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun K _ => sum_congr rfl fun k _ => by ring
    _ = _ := by
        simp only [qx_ps_equiv hd hmu hnu, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun I' _ => sum_congr rfl fun K _ => by ring

lemma qx_rank (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) :
    Fintype.card M'.ι = ∑ x : qx_J Str CF, dMu (x.2 : Fin n → ℤ) := by
  rw [Fintype.card_congr e, Fintype.card_prod, CF.rank, sum_mul, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [hd.2.2.2.2.2 _ (CF.dom j)]
  exact (Finset.sum_coe_sort (Str (CF.mu j)) dMu).symm

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

