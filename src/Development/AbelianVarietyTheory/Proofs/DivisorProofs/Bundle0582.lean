import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantElementProperty
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isTheta_unique {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {σ : Λ →+* O} {f f' : RL p O Λ →+* O} (hf : IsTheta σ f) (hf' : IsTheta σ f') : f = f' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a l => rw [hf, hf']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_detElt_lieRank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ ∧ HasOrders C ε N Δ D.lieRank c ∧ v (c τ) = v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^ D.lieRank τ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N h hh D τ ι lam hι hlat
  classical
  obtain ⟨Φ⟩ := GlobalTheory.T.determinant_frame_comparison_unit p C v O hv ε hε Λ N h hh D ψ hψ
  obtain ⟨-, -, -, -, -, hxi, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  let c : (Λ →+* O) → C := fun σ =>
    if hσ : ∃ f, IsTheta σ f then
      Classical.choose (GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec).2
    else 0
  have hc : ∀ σ f, IsTheta σ f → D.lieRank σ ≤ N ∧ c σ ≠ 0 ∧
      Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) (c σ) := by
    intro σ f hf
    have hσ : ∃ f, IsTheta σ f := ⟨f, hf⟩
    have hfe : hσ.choose = f := isTheta_unique hσ.choose_spec hf
    have H := GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec
    have hcs := Classical.choose_spec H.2
    have hcσ : c σ = Classical.choose H.2 := by simp only [c, dif_pos hσ]
    rw [hcσ]
    refine ⟨H.1, hcs.1, ?_⟩
    rw [← hfe]
    exact hcs.2
  have hψdet : ψ Φ.F.det = (Φ.F.map ψ).det := by rw [RingHom.map_det]; rfl
  refine ⟨Φ.F.det, c, ⟨⟨Φ.G.det, ?_⟩, Φ.Ψ.det, ?_, ⟨Φ.Ψ'.det, ?_⟩⟩, fun σ f hf => hc σ f hf, ?_⟩
  · rw [← Matrix.det_mul, Φ.F_mul_G, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · rw [hψdet, ← Matrix.det_mul, ← Φ.F_eq]
  · rw [← Matrix.det_mul, Φ.Ψ_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · obtain ⟨f, hf, -, -, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
    obtain ⟨l₀, hl₀, hiota⟩ := GlobalTheory.T.determinant_valuation_order_sum p C v O hv ε hε Λ N h hh D ψ Φ τ f hf ι lam hι hlat
    have hrank := GlobalTheory.T.determinant_valuation_order p C v O hv ε hε Λ N h hh D ψ Φ τ f hf
    have hmu : (inA (mu ε) : RL p O Λ) = (inA (xi ε) : RL p O Λ) * inA (nu ε) := by
      rw [← map_mul, xi_mul_nu]
    have hFG : Φ.F * Φ.G =
        ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
      rw [Φ.F_mul_G, hmu]
    rw [← hrank] at hiota
    have hlead := GlobalTheory.LeadDet.lead_det (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      (inA (nu ε)) N Φ.F Φ.G l₀ hFG hiota
    rw [hrank] at hlead
    obtain ⟨-, -, hcl⟩ := hc τ f hf
    have hξreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
      GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hxi
    have heq := GlobalTheory.DetInv.lead_mul_unique (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      Φ.F.det 1 (D.lieRank τ) _ (c τ) hξreg hlead (by rwa [one_mul])
    have hA : f (inA (nu ε)) = WittVector.fontaineTheta O p (nu ε) := by
      show f (algebraMap (Ainf p O) (RL p O Λ) (nu ε)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, hf]
      simp
    rw [heq, map_one, one_mul, map_mul, map_pow, hl₀, RingHom.comp_apply, hA]

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientLineDegreeLeOfTriangularFamily
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.QuotLine

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem det_fac {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hM : ∀ i : Fin r, M i.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hM]

theorem val_corner {r : ℕ} (v : Place k K) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hM : ∀ i : Fin r, M i.succ 0 = 0) (h1 : Unimod v M)
    (h2 : Unimod v (M.submatrix Fin.succ Fin.succ)) : v.1 (M 0 0) = 1 := by
  have h := h1.2
  rw [det_fac M hM, map_mul, h2.2, mul_one] at h
  exact h

theorem nrm_cons {n : ℕ} (v : Place k K) (x : K) (y : Fin n → K) :
    nrm v (Fin.cons x y : Fin (n + 1) → K) = max (v.1 x) (nrm v y) := by
  simp only [nrm, Fin.univ_succ, Finset.sup_cons, Finset.sup_map, Fin.cons_zero]
  rfl

theorem nrm_two (v : Place k K) (x y : K) : nrm v ![x, y] = max (v.1 x) (v.1 y) := by
  have h1 := nrm_cons v x ![y]
  have h2 := nrm_cons v y ![]
  have h3 : nrm v (![] : Fin 0 → K) = 0 := by simp [nrm]
  rw [h3, max_eq_left (zero_le' )] at h2
  exact h1.trans (by rw [← h2]; rfl)

theorem quot_line_le : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → (∀ (v : Place k F) (i : Fin r), g v i.succ 0 = 0) → admitted (fun v => (g v).submatrix Fin.succ Fin.succ) → ∀ b : ℝ, LinesLE g b → LinesLE (fun v => (g v).submatrix Fin.succ Fin.succ) (2 * b - (∑ᶠ v, ord v (g v 0 0) : ℤ)) := by
  intro k F _ _ _ _ _ hF r g hg hg0 hh b hb E _ _ _ _ _ ρ hρ m hm
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
  obtain ⟨hGa, -, -, hGL⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
  obtain ⟨hQa, -, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ r _ hh
  have hGb := hGL b hb

  have hcF : ∀ v, Unimod v (g v) → Unimod v ((g v).submatrix Fin.succ Fin.succ) → v.1 (g v 0 0) = 1 :=
    fun v h1 h2 => val_corner v (g v) (hg0 v) h1 h2
  have ha0 : ∀ v, g v 0 0 ≠ 0 := by
    intro v h0; apply hg.1 v; rw [det_fac (g v) (hg0 v), h0, zero_mul]
  obtain ⟨a1, ha1def⟩ : ∃ a1 : Place k F → Matrix (Fin 1) (Fin 1) F, a1 = fun v => !![g v 0 0] := ⟨_, rfl⟩
  have ha1 : admitted a1 := by
    refine ⟨fun v => by simp [ha1def, ha0 v], (hg.2.union hh.2).subset ?_⟩
    intro v hv
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    have h1 := hcF v hno.1 hno.2
    apply hv
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i; fin_cases j; simp [ha1def, h1]
    · simp [ha1def, h1]
  obtain ⟨-, hdeg1, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ 1 a1 ha1
  generalize hGdef : pullAd ρ g = G at hGa hGb
  generalize hQdef : pullAd ρ (fun v => (g v).submatrix Fin.succ Fin.succ) = Q at hQa ⊢
  have hQG : ∀ p, Q p = (G p).submatrix Fin.succ Fin.succ := by
    intro p; rw [← hQdef, ← hGdef]; rfl
  have hG0 : ∀ p (i : Fin r), G p i.succ 0 = 0 := by
    intro p i; rw [← hGdef]; simp [pullAd, hg0]
  have hS : ∑ᶠ p, ord p (G p 0 0) = Module.finrank F E * ∑ᶠ v, ord v (g v 0 0) := by
    have e1 : deg (pullAd ρ a1) = ∑ᶠ p, ord p (G p 0 0) := by
      unfold deg; apply finsum_congr; intro p; rw [← hGdef]; simp [pullAd, ha1def]
    have e2 : deg a1 = ∑ᶠ v, ord v (g v 0 0) := by
      unfold deg; apply finsum_congr; intro v; simp [ha1def]
    rw [← e1, hdeg1, e2]
  obtain ⟨-, hQm⟩ := GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE r Q hQa
  obtain ⟨hfinQm, hnz⟩ := hQm m hm
  have hord := fun p : Place k E => GlobalTheory.T.functionFieldPlaceOrder_calculus k E p
  choose idx hidx using fun p : Place k E => (hord p).2.2.2.2.2.2.1 r (Q p *ᵥ m) (hnz p)
  obtain ⟨t, ht⟩ : ∃ t : Place k E → Matrix (Fin 2) (Fin 2) E, t = fun p =>
      !![G p 0 0, ∑ j : Fin r, G p 0 j.succ * m j; 0, (Q p *ᵥ m) (idx p)] := ⟨_, rfl⟩
  have hdett : ∀ p, (t p).det = G p 0 0 * (Q p *ᵥ m) (idx p) := by
    intro p; rw [ht, Matrix.det_fin_two_of]; ring
  have hG00 : ∀ p, G p 0 0 ≠ 0 := by
    intro p h0; apply hGa.1 p; rw [det_fac (G p) (hG0 p), h0, zero_mul]
  have hcE : ∀ p, Unimod p (G p) → Unimod p (Q p) → p.1 (G p 0 0) = 1 :=
    fun p h1 h2 => val_corner p (G p) (hG0 p) h1 (by rw [← hQG]; exact h2)
  have hmfin : ∀ j, {p : Place k E | ¬ p.1 (m j) ≤ 1}.Finite := by
    intro j
    by_cases hj : m j = 0
    · simp [hj]
    · exact ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (m j) hj).1).subset fun p hp h1 => hp (le_of_eq h1)
  have hta : admitted t := by
    refine ⟨fun p => by rw [hdett]; exact mul_ne_zero (hG00 p) (hidx p).1, ?_⟩
    refine ((hGa.2.union hQa.2).union (hfinQm.union (Set.finite_iUnion hmfin))).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hno
    obtain ⟨⟨hGu, hQu⟩, hn1, hmj⟩ := hno
    apply hp
    have hc1 : p.1 (G p 0 0) = 1 := hcE p hGu hQu
    have hm1 : p.1 ((Q p *ᵥ m) (idx p)) = 1 := by rw [← (hidx p).2.1]; exact hn1
    have hcs : p.1 (∑ j : Fin r, G p 0 j.succ * m j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hGu.1 0 j.succ) (hmj j)
    refine ⟨fun i j => ?_, ?_⟩
    · rw [ht]; fin_cases i <;> fin_cases j <;> simp [hc1, hm1, hcs]
    · rw [hdett, map_mul, hc1, hm1, one_mul]
  have htL : LinesLE t (b * Module.finrank F E) := by
    intro E' _ _ _ _ _ ρ' hρ' w hw
    have hres := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k E E').2 ρ' hρ'
    obtain ⟨w', hw'def⟩ : ∃ w' : Fin (r + 1) → E', w' = Fin.cons (w 0) (fun j => w 1 * algebraMap E E' (m j)) :=
      ⟨_, rfl⟩
    have hw' : w' ≠ 0 := by
      intro h0
      apply hw
      have h00 : w 0 = 0 := by simpa [hw'def] using congr_fun h0 0
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hm (funext hc)
      have h1 : w 1 * algebraMap E E' (m j) = 0 := by simpa [hw'def] using congr_fun h0 j.succ
      have h11 : w 1 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd ((map_eq_zero_iff _ (algebraMap E E').injective).1 h) hj
      ext i; fin_cases i <;> simp [h00, h11]
    have hloc : ∀ p', nrm p' (pullAd ρ' t p' *ᵥ w) = nrm p' (pullAd ρ' G p' *ᵥ w') := by
      intro p'
      obtain ⟨e, -, he, -⟩ := hres p'
      have v1 : pullAd ρ' t p' *ᵥ w = ![algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1,
          algebraMap E E' ((Q (ρ' p') *ᵥ m) (idx (ρ' p'))) * w 1] := by
        ext i; fin_cases i <;> simp [pullAd, ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have v2 : pullAd ρ' G p' *ᵥ w' = Fin.cons (algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1)
          (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext i; refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hw'def, Fin.cons_zero, Fin.cons_succ,
            pullAd, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Fin.cases_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        · simp [pullAd, hw'def, hQG, hG0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_sum,
            Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      rw [v1, v2, nrm_two, nrm_cons]
      congr 1
      have hs : (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) =
          w 1 • (fun i => algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext; simp [smul_eq_mul]
      rw [hs, (GlobalTheory.T.functionFieldPlaceOrder_calculus k E' p').2.2.2.2.2.2.2.1, map_mul, mul_comm]
      congr 1
      apply le_antisymm
      · exact Finset.le_sup (f := fun i => p'.1 (algebraMap E E' ((Q (ρ' p') *ᵥ m) i)))
          (Finset.mem_univ (idx (ρ' p')))
      · apply Finset.sup_le; intro j _
        rw [he, he]; exact pow_le_pow_left' ((hidx (ρ' p')).2.2.2 j) e
    have heq : degLine (pullAd ρ' t) w = degLine (pullAd ρ' G) w' := by
      simp only [degLine, ordVec, hloc]
    rw [heq]; exact hGb E' ρ' hρ' w' hw'
  have hdeg := GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular k E hE t hta (fun p => by simp [ht]) _ htL
  have hs1 : (Function.support fun p : Place k E => ord p (G p 0 0)).Finite := by
    refine (hGa.2.union hQa.2).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    apply hp
    simp [ord, hcE p hno.1 hno.2]
  have hs2 : (Function.support fun p : Place k E => ordVec p (Q p *ᵥ m)).Finite := by
    refine hfinQm.subset ?_
    intro p hp hn
    apply hp
    simp [ordVec, hn]
  have hsplit : deg t = (∑ᶠ p, ord p (G p 0 0)) + degLine Q m := by
    unfold deg degLine
    rw [← finsum_add_distrib hs1 hs2]
    apply finsum_congr; intro p
    rw [hdett, (hord p).1 _ _ (hG00 p) (hidx p).1, (hidx p).2.2.1]
  rw [hS] at hsplit
  have hc : (degLine Q m : ℝ) = (deg t : ℝ) - (Module.finrank F E : ℝ) * ((∑ᶠ v, ord v (g v 0 0) : ℤ) : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [hc]
  nlinarith [hdeg]

end GlobalTheory.Nef.QuotLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CommonValuation

theorem exists_eq_pow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

theorem exists_dvr (V K L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra W L)
      (_ : IsFractionRing W L) (f : V →+* W), (∀ z : V, algebraMap W L (f z) = algebraMap K L (algebraMap V K z)) ∧
      ∀ z : V, f z ∈ IsLocalRing.maximalIdeal W ↔ z ∈ IsLocalRing.maximalIdeal V := by
  let _ : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDedekindDomain (integralClosure V L) := integralClosure.isDedekindDomain V K L
  have : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hinj : Function.Injective (algebraMap V (integralClosure V L)) := fun a b h =>
    IsFractionRing.injective V K ((algebraMap K L).injective (congrArg Subtype.val h))
  obtain ⟨M, -, hM, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure V L)
    (IsLocalRing.maximalIdeal V) ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have h0 : M ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hc
    exact IsDiscreteValuationRing.not_a_field V hc.symm
  let P : HeightOneSpectrum (integralClosure V L) := ⟨M, hM, h0⟩
  refine ⟨(P.valuation L).valuationSubring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap V L).codRestrict (P.valuation L).valuationSubring.toSubring
      (fun z => P.valuation_le_one (K := L) (algebraMap V _ z)), fun _ => rfl, fun z => ?_⟩
  rw [Valuation.mem_maximalIdeal_iff, ← hc]
  exact P.valuation_lt_one_iff_mem (K := L) (algebraMap V _ z)

theorem le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top

theorem exists_centre {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h

theorem exists_common_valuation : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by
  intro k k' _ _ _ _ i 𝔭 𝔓 ε V K _ _ _ _ _ _ em e hε he hem
  let _ : Algebra k k' := i.toAlgebra
  let N := IntermediateField.normalClosure k k' (AlgebraicClosure k')
  have : NumberField N := NumberField.of_module_finite k N
  obtain ⟨L, _, _, j, _, _, hj⟩ := exists_finite_separable_compositum k K N em
  have hj' : ∀ z, j (algebraMap k N z) = algebraMap K L (em z) := fun z => DFunLike.congr_fun hj z
  obtain ⟨W, _, _, _, _, _, f, hf, hfm⟩ := exists_dvr V K L
  let w := (IsDiscreteValuationRing.maximalIdeal W).valuation L
  obtain ⟨d, hd, hdv⟩ := exists_eq_pow (IsDiscreteValuationRing.maximalIdeal V) (w.comap (algebraMap K L))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact (IsDiscreteValuationRing.maximalIdeal W).valuation_le_one (f r))
    (fun r => by
      rw [Valuation.comap_apply, ← hf]
      exact ((IsDiscreteValuationRing.maximalIdeal W).valuation_lt_one_iff_mem (K := L) (f r)).trans (hfm r))
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simpa using hε 0
  obtain ⟨Q, hQ, hQm⟩ := exists_centre (w.comap j)
  obtain ⟨Q', hQ', hQo⟩ := (inferInstance : Nonempty (𝔓.asIdeal.primesOver (𝓞 N)))
  have hpow : ∀ {x : WithZero (Multiplicative ℤ)} {n : ℕ}, n ≠ 0 → (x ^ n < 1 ↔ x < 1) := fun hn =>
    pow_lt_one_iff_of_nonneg zero_le hn
  have hund : Q.under (𝓞 k) = Q'.under (𝓞 k) := by
    ext r
    rw [← Ideal.under_under (B := 𝓞 k') Q', ← hQo.over]
    change algebraMap _ _ r ∈ Q ↔ algebraMap _ _ r ∈ 𝔓.asIdeal
    rw [hQm, ← 𝔓.valuation_lt_one_iff_mem (K := k')]
    change w (j (algebraMap k N r)) < 1 ↔ 𝔓.valuation k' (i r) < 1
    rw [hj', hε, hpow hε0]
    change w.comap (algebraMap K L) _ < 1 ↔ _
    rw [hdv, hem, hpow hd.ne', hpow he.ne']
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 k) (𝓞 N) (N ≃ₐ[k] N) Q' Q hund.symm
  let em' : k' →+* L := j.comp (σ.toRingEquiv.toRingHom.comp (algebraMap k' N))
  have hc : ∀ z, em' (i z) = algebraMap K L (em z) := fun z => by
    rw [← hj', ← σ.commutes z, IsScalarTower.algebraMap_apply k k' N]
    rfl
  obtain ⟨e', he', hv⟩ := exists_eq_pow 𝔓 (w.comap em') (le_one_of_ringOfIntegers _) (fun r => by
    rw [hQo.over]
    change _ ↔ algebraMap _ _ r ∈ Q'
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), ← hσ, hQm]
    rfl)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, f,
    algebraMap K L, em', e', d, hf, RingHom.ext hc, he', ?_, hv, hdv⟩
  obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer k
  have h1 := hv (i π)
  rw [Valuation.comap_apply, hc, hε] at h1
  have h2 := hdv (em π)
  rw [Valuation.comap_apply, h1, hem, hπ, ← pow_mul, ← pow_mul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    WithZero.exp_inj] at h2
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_inj, Nat.cast_inj] at h2
  rw [mul_comm, h2, mul_comm]

end GlobalTheory.CommonValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCongruenceSubgroupsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_congruence_subgroups : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  first | exact @GlobalTheory.UCls.exists_special_reduction | exact GlobalTheory.UCls.exists_special_reduction | (intros; apply GlobalTheory.UCls.exists_special_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProdStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)), FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  first | exact @GlobalTheory.sncAt_of_stalkId_eq_span_prod | exact GlobalTheory.sncAt_of_stalkId_eq_span_prod | (intros; apply GlobalTheory.sncAt_of_stalkId_eq_span_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T], IsUnit (q : T) → ∀ (i : ℤ) (y : Ht q (sp (LaurentPolynomial T)) 0 i), ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y := by
  first | (exact @GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (exact GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (intros; apply GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (exact GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (intros; apply GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeOmActKronBlockDiagonalLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockBlockDeg

theorem Jm_apply_of_ne {r s : ℕ} {c e : Ix r s} (h : c ≠ e) : Jm r s c e = 0 := by
  rcases c with c | c <;> rcases e with e | e <;>
    simp_all [Jm, Formalism.UG.Jpq]

theorem totalDegree_omAct_kron_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  intro p q r s E hE d P hP
  rw [← mem_restrictTotalDegree] at hP ⊢
  refine GlobalTheory.FockPolGK.omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change E a b * Jm r s c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hE a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Jm_apply_of_ne hc, mul_zero]

end GlobalTheory.FockBlockDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodLocalVolumeFactorLeZetaStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_local_volume_factor_le_zeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r → Multipliable (GlobalTheory.SUVol.locFactor E r) → ∏' v, GlobalTheory.SUVol.locFactor E r v ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  first | exact @GlobalTheory.EulerLocVol.tprod_locFactor_le | exact GlobalTheory.EulerLocVol.tprod_locFactor_le | (intros; apply GlobalTheory.EulerLocVol.tprod_locFactor_le <;> assumption)
end

