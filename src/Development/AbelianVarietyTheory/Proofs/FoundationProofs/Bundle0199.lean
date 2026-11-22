import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenform
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem slz_const_mul (k : ℕ) (δ : M2) (c : ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => c * g σ) τ = c * slz k δ g τ := by
  unfold slz; ring

private theorem slz_sub (k : ℕ) (δ : M2) (g g' : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => g σ - g' σ) τ = slz k δ g τ - slz k δ g' τ := by
  unfold slz; ring

private theorem slz_sum {ι : Type} (s : Finset ι) (k : ℕ) (δ : M2) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i ∈ s, g i σ) τ = ∑ i ∈ s, slz k δ (g i) τ := by
  unfold slz; rw [Finset.mul_sum]

theorem qs_Vo_slz (k l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    qs (Vo l a) τ = ((l : ℂ) ^ (k - 1))⁻¹ * slz k !![(l : ℤ), 0; 0, 1] (qs a) τ := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have him : 0 < ((l : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hl) τ.im_pos
  have hV := (GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl ha).2 τ ⟨(l : ℂ) * τ, him⟩ rfl
  rw [hV]
  unfold slz
  simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  simp only [zero_mul, zero_add, mul_one, mul_zero, sub_zero, add_zero, div_one, one_pow, inv_one]
  rw [ofComplex_apply_of_im_pos him]
  field_simp

end GlobalTheory.EisM

namespace GlobalTheory.EisM

private theorem qs_smul (t : ℂ) (a : ℕ → ℂ) : qs (t • a) = fun τ => t * qs a τ := by
  funext τ; unfold qs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem sum_slz_repL_Vo : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  intro k N l ε h t hk hN hl hlN hMF hT τ
  have hl0 : 0 < l := hl.pos
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  set F := qs h with hF
  set D : M2 := !![(l : ℤ), 0; 0, 1] with hD
  set E : M2 := !![(1 : ℤ), 0; 0, (l : ℤ)] with hE
  have hcoc := GlobalTheory.T.slashIntMatrixPosDet_properties k

  have hTq := (GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k l (ch ε) h hk hl0 (by simp [ch]) hMF.1).2
  rw [hT, qs_smul] at hTq
  have hind := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k N N ε (DT N l) (Option (Fin l)) (Option (Fin l)) (repT l) (repL N l) F hk dvd_rfl
    (fun δ hδ => ⟨by rw [hδ.1]; exact_mod_cast hl0, hδ.2⟩) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator N l hl hlN) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel N l hl hlN) hMF.2
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hu : IsUnit (((l : ℤ) : ZMod N)) := by
    rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime l N).2 hcop
  have hεl : ch ε l ≠ 0 := by
    unfold ch; exact (IsUnit.map ε hu).ne_zero
  have hinv : ch ε⁻¹ l = (ch ε l)⁻¹ := by
    unfold ch; rw [MulChar.inv_apply_eq_inv']
  have key : ∀ σ : ℍ, ∑ j : Fin l, slz k (repL N l (some j)) F σ = (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    intro σ
    have h1 := congrFun hTq σ
    rw [hind] at h1
    unfold hsum at h1
    rw [Fintype.sum_option] at h1
    have h2 : repL N l none = E := rfl
    rw [h2] at h1
    have h3 : ∀ j : Fin l, ch ε (repL N l (some j) 0 0) = ch ε l := by
      intro j; simp [repL]
    have h4 : ch ε (E 0 0) = 1 := by simp [hE, ch]
    simp only [h3, h4, one_mul, ← Finset.mul_sum] at h1
    field_simp
    rw [← hF] at h1
    linear_combination -h1
  have hVfun : qs (Vo l h) = fun σ => ((l : ℂ) ^ (k - 1))⁻¹ * slz k D F σ := by
    funext σ; exact qs_Vo_slz k l hl0 h hMF.1 σ
  have hdetD : 0 < D.det := by simp [hD, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetE : 0 < E.det := by simp [hE, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetA : ∀ (L : ℕ) (j : Fin l), 0 < (repL L l (some j)).det := by
    intro L j; simp [repL, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hmat : ∀ j : Fin l, D * repL (N * l) l (some j) = repL N l (some j) * D := by
    intro j
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring
  have hED : E * D = !![((l : ℕ) : ℤ), 0; 0, ((l : ℕ) : ℤ)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ =
      ((l : ℂ) ^ (k - 1))⁻¹ * slz k D (slz k (repL N l (some j)) F) τ := by
    intro j
    rw [hVfun, slz_const_mul]
    congr 1
    rw [← (hcoc F hk).1 D _ hdetD (hdetA _ j), hmat j, (hcoc F hk).1 _ D (hdetA _ j) hdetD]
  simp only [hterm]
  rw [← Finset.mul_sum, ← slz_sum]
  have hfun : (fun σ => ∑ j : Fin l, slz k (repL N l (some j)) F σ) = fun σ => (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    funext σ; exact key σ
  rw [hfun, slz_const_mul, slz_sub, slz_const_mul]
  have hDE : slz k D (slz k E F) τ = (l : ℂ) ^ k / (l : ℂ) ^ 2 * F τ := by
    rw [← (hcoc F hk).1 E D hdetE hdetD, hED]
    exact (hcoc F hk).2.2.2.2 l τ hl0
  rw [hDE, hinv]
  have hV := qs_Vo_slz k l hl0 h hMF.1 τ
  rw [hV]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitriMonomialOfLowerTri
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.CoeffWord

variable {R : Type} [CommRing R] {r n : ℕ}

def unitri (R : Type) [CommRing R] (L : List (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => if v.1.val = v.2.val then 1 else if v ∈ L then X v else 0

def single (R : Type) [CommRing R] (p : Fin r × Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => if v = p then Polynomial.X else Polynomial.C (X v)

theorem single_monomial (p : Fin r × Fin n) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    single R p (monomial m c) = Polynomial.monomial (m p) (monomial (m.erase p) c) := by
  classical
  have h1 : (monomial m c : MvPolynomial (Fin r × Fin n) R) = monomial (m.erase p) c * X p ^ (m p) := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
  have h2 : single R p (monomial (m.erase p) c) = Polynomial.C (monomial (m.erase p) c) := by
    rw [single, aeval_monomial, monomial_eq, map_mul, map_finsuppProd]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v ≠ p := by
      rintro rfl
      simp at hv
    simp [this]
  have h3 : single R p (X p) = Polynomial.X := by simp [single]
  rw [h1, map_mul, map_pow, h2, h3, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_single (p : Fin r × Fin n) (e : Fin r × Fin n →₀ ℕ) (he : e p = 0) (k : ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) :
    coeff e ((single R p G).coeff k) = coeff (e + Finsupp.single p k) G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | add G H hG hH => simp [hG, hH]
  | monomial m c =>
    rw [single_monomial, Polynomial.coeff_monomial, coeff_monomial]
    by_cases h : m = e + Finsupp.single p k
    · have h1 : m p = k := by simp [h, he]
      have h2 : m.erase p = e := by
        ext v
        by_cases hv : v = p
        · simp [hv, he]
        · simp [h, Finsupp.erase_ne hv, Finsupp.single_apply, Ne.symm hv]
      simp [h1, h2, ← h]
    · rw [if_neg h]
      split_ifs with h1
      · rw [coeff_monomial, if_neg]
        intro h2
        apply h
        rw [← h2, ← h1, Finsupp.erase_add_single]
      · simp

theorem map_rowGen (L : List (Fin r × Fin n)) (p : Fin r × Fin n) (s : Fin r) (hs : s.val = p.2.val)
    (hp : p.2.val < p.1.val) (hpL : p ∉ L) (hL : ∀ q ∈ L, q.2.val < q.1.val ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    (rowGen R s p.1 F).map (unitri R L).toRingHom = single R p (unitri R (L ++ [p]) F) := by
  have : (Polynomial.mapRingHom (unitri R L).toRingHom).comp (rowGen R s p.1).toRingHom =
      (single R p).toRingHom.comp (unitri R (L ++ [p])).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp [rowGen, single, unitri]
    · by_cases hv : v = p
      · subst hv
        simp [rowGen, single, unitri, hs, hp.ne', hpL]
      · have h0 : v.1 = p.1 → unitri R L (X (s, v.2)) = 0 := by
          intro h1
          have h2 : v.2.val ≠ p.2.val := fun h => hv (Prod.ext h1 (Fin.ext h))
          have h3 : (s, v.2) ∉ L := fun h => by
            have := hL _ h
            simp only at this
            omega
          have h4 : s.val ≠ v.2.val := by omega
          simp [unitri, h3, h4]
        have h5 : single R p (unitri R (L ++ [p]) (X v)) = Polynomial.C (unitri R L (X v)) := by
          simp only [unitri, aeval_X, List.mem_append, List.mem_singleton, hv, or_false]
          split_ifs <;> simp [single, hv]
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h5, rowGen, aeval_X,
          Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_C]
        split_ifs with h1
        · simp [h0 h1]
        · simp
  exact RingHom.congr_fun this F

def letter (e : Fin r × Fin n →₀ ℕ) (p : Fin r × Fin n) : Fin r × Fin r × ℕ :=
  (if h : p.2.val < r then ⟨p.2.val, h⟩ else p.1, p.1, e p)

theorem eval_applyWord (e : Fin r × Fin n →₀ ℕ) (L : List (Fin r × Fin n))
    (h1 : ∀ q ∈ L, q.2.val < q.1.val) (h2 : L.Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    eval (idFrame R r n) (applyWord R (L.map (letter e)) F) =
      coeff (e.filter (· ∈ L)) (unitri R L F) := by
  induction L using List.reverseRecOn generalizing F with
  | nil =>
    have h : (eval (idFrame R r n)) = constantCoeff.comp (unitri R ([] : List (Fin r × Fin n))).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
      · simp [unitri]
      · simp only [unitri, idFrame, eval_X, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        split_ifs <;> simp_all
    have h' : e.filter (· ∈ ([] : List (Fin r × Fin n))) = 0 := by
      ext v; simp
    rw [h', h]
    rfl
  | append_singleton L p ih =>
    rw [List.pairwise_append] at h2
    obtain ⟨h2, -, h3⟩ := h2
    have hp := h1 p (by simp)
    have hpr : p.2.val < r := lt_trans hp p.1.2
    have hL1 : ∀ q ∈ L, q.2.val < q.1.val := fun q hq => h1 q (by simp [hq])
    have hpL : p ∉ L := fun h => (h3 p h p (by simp)).1 rfl
    have hw : applyWord R ((L ++ [p]).map (letter e)) F =
        applyWord R (L.map (letter e)) (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) := by
      simp [applyWord, letter, hpr]
    rw [hw, ih hL1 h2]
    have hm := map_rowGen (R := R) L p ⟨p.2.val, hpr⟩ rfl hp hpL
      (fun q hq => ⟨hL1 q hq, (h3 q hq p (by simp)).2⟩) F
    have hc := congrArg (fun P => Polynomial.coeff P (e p)) hm
    simp only [Polynomial.coeff_map] at hc
    have hc' : unitri R L (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) =
        (single R p (unitri R (L ++ [p]) F)).coeff (e p) := hc
    rw [hc', coeff_single _ _ (by simp [Finsupp.filter_apply, hpL])]
    congr 1
    ext v
    by_cases hv : v = p
    · subst hv; simp [Finsupp.filter_apply, hpL]
    · simp [Finsupp.filter_apply, hv, Finsupp.single_apply, Ne.symm hv]

def positions (r n : ℕ) : List (Fin r × Fin n) :=
  (List.finRange n).reverse.flatMap fun s =>
    ((List.finRange r).filter fun a => s.val < a.val).map fun a => (a, s)

theorem mem_positions (v : Fin r × Fin n) : v ∈ positions r n ↔ v.2.val < v.1.val := by
  obtain ⟨a, s⟩ := v
  simp [positions]

theorem wordOf_eq (e : Fin r × Fin n →₀ ℕ) : wordOf e = (positions r n).map (letter e) := by
  rw [wordOf, positions, List.map_flatMap]
  congr 1
  funext s
  rw [List.map_map]
  generalize List.finRange r = l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : s.val < a.val
    · have hr : s.val < r := lt_trans h a.2
      rw [List.filterMap_cons, dif_pos ⟨h, hr⟩, List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, ih]
      simp [letter, hr]
    · rw [List.filterMap_cons, dif_neg (fun h' => h h'.1), List.filter_cons_of_neg (by simpa using h)]
      exact ih

theorem pairwise_positions :
    (positions r n).Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val := by
  rw [positions, List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ ((List.nodup_finRange r).filter _)
    intro a b hab
    exact ⟨fun h => hab (congrArg Prod.fst h), le_rfl⟩
  · rw [List.pairwise_reverse]
    refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange n)
    intro s t hst x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    exact ⟨fun h => hst.ne' (congrArg Prod.snd h), hst.le⟩

theorem eq_of_filter_eq (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hs : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s))
    (h : ∀ v : Fin r × Fin n, v.2.val < v.1.val → m v = e v) : m = e := by
  have key : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [hm a s h1, he a s h1]
    · exact h (a, s) h1
  ext ⟨a, s⟩
  by_cases ha : a.val = s.val
  · have h1 := hs s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      Finset.sum_congr rfl (fun b hb => key b s (fun hb' =>
        (Finset.ne_of_mem_erase hb) (Fin.ext (hb'.trans ha.symm))))] at h1
    exact Nat.add_right_cancel h1
  · exact key a s ha

theorem unitri_monomial_of_lowerTri (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = monomial (m.filter (· ∈ positions r n)) c := by
  classical
  rw [unitri, aeval_monomial, monomial_eq, Finsupp.prod_filter_index, Finsupp.support_filter,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  have h1 : ¬ v.1.val < v.2.val := fun h => hv' (hm v.1 v.2 h)
  by_cases h2 : v.1.val = v.2.val
  · simp [mem_positions, h2]
  · have h3 : v.2.val < v.1.val := by omega
    simp [mem_positions, h2, h3]

theorem unitri_monomial_of_not (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = 0 := by
  simp only [LowerTri, not_forall] at hm
  obtain ⟨a, s, h, h0⟩ := hm
  rw [unitri, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero (i := (a, s)) (Finsupp.mem_support_iff.2 h0), mul_zero]
  have h1 : ¬ s.val < a.val := by omega
  simp [mem_positions, h.ne, h1, h0]

theorem weight_colW (m : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) m s = ∑ a : Fin r, m (a, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

theorem coeffWord : Formalism.GradedWeylDivisibility.CoeffWord := by
  classical
  intro R _ r n ν F e hF he hν
  rw [wordOf_eq, eval_applyWord e _ (fun q hq => (mem_positions q).1 hq) pairwise_positions]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, coeff_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (colW r n) m = ν := hF (mem_support_iff.1 hm)
  by_cases hl : LowerTri m
  · rw [unitri_monomial_of_lowerTri m hl, coeff_monomial, coeff_monomial]
    refine if_congr ⟨fun h => by rw [h], fun h => ?_⟩ rfl rfl
    refine eq_of_filter_eq m e hl he (fun s => by rw [← weight_colW, hw, hν]) fun v hv => ?_
    have := DFunLike.congr_fun h v
    simpa [Finsupp.filter_apply, mem_positions, hv] using this
  · rw [unitri_monomial_of_not m hl, coeff_monomial, if_neg (fun h : m = e => hl (h ▸ he)), coeff_zero]

end GlobalTheory.CoeffWord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

noncomputable section

namespace GlobalTheory.EmbInj

open Formalism.BasicNotions.Loc

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_iff_norm (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (LL : FinExt l) (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [← isIntegral_iff_norm, OL, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm

theorem norm_algHom (K L : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
  [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

theorem norm_le_one_iff (y : ↥B.LL.1) : ‖(y : Om l)‖ ≤ 1 ↔ ∃ n : O, y = B.toLL n := by
  rw [← mem_OL_iff]
  constructor
  · intro h
    refine ⟨B.eO.symm ⟨y, h⟩, ?_⟩
    simp [LocBridge.toLL]
  · rintro ⟨n, rfl⟩
    exact (B.eO n).2

theorem toLL_inj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)

theorem exists_frac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
  by_cases h : ‖(y : Om l)‖ ≤ 1
  · obtain ⟨n, hn⟩ := (norm_le_one_iff B y).1 h
    refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
    have := congrArg B.toLL h1
    simp at this
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
    obtain ⟨d, hd⟩ := (norm_le_one_iff B _).1 h'
    refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
    rw [h1, map_zero] at hd
    exact hy (inv_eq_zero.1 hd)

theorem algHom_ext (τ τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1)
    (h : ∀ x : E, τ ⟨B.j (algebraMap E Ω x), B.j_E x⟩ = τ' ⟨B.j (algebraMap E Ω x), B.j_E x⟩) :
    τ = τ' := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz
  have e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) =
      ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1) := by
    rw [map_sub, map_sub, hz, h x]
    push_cast
    ring
  have h1 := norm_algHom _ _ τ (y - z)
  have h2 := norm_algHom _ _ τ' (y - z)
  have h3 := norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)
  have h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

end Local

theorem valuation_lt_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (x : Ω) :
    A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  by_cases hx : x = 0
  · simp [hx]
  · have : A.valuation x ≠ 0 := by simpa using hx
    rw [← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 this)]
    simp [hx]

end GlobalTheory.EmbInj
end
end

