import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IntegralMultipleCoprime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def unitBall (p : ℕ) [Fact p.Prime] : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (PadicAlgCl.isNonarchimedean p a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

private theorem den_of_norm {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℚ_[p])‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))
  have hd1 : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have heq : (q : ℚ_[p]) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hn := congrArg norm heq
  rw [norm_mul, hn1] at hn
  nlinarith [norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]

private theorem coeff_den {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ τ : F →+* PadicAlgCl p, ‖τ x‖ ≤ 1) (i : ℕ) : ¬ p ∣ ((minpoly ℚ x).coeff i).den := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP
  have hPm : P.Monic := (minpoly.monic hx).map _
  have hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1 := by
    intro r hr
    have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p) := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hx, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hPm.ne_zero).mp hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact h ψ.toRingHom
  have hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have hlift : P ∈ Polynomial.lifts (unitBall p).subtype := by
    rw [← hprod]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
    exact ⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).mp hlift i
  have hn : ‖P.coeff i‖ ≤ 1 := by
    rw [← hy]
    exact y.2
  rw [hP, Polynomial.coeff_map] at hn
  apply den_of_norm
  have hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i)
      = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p]) := by
    simp only [eq_ratCast, map_ratCast]
  rw [hc] at hn
  exact (PadicAlgCl.norm_extends p _).symm.trans_le hn

private theorem integral_multiple_coprime {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ i, ¬ p ∣ ((minpoly ℚ x).coeff i).den) :
    ∃ (m : ℕ) (c : 𝓞 F), m.Coprime p ∧ (c : F) = m * x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := minpoly ℚ x with hP
  set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM
  have hMcop : M.Coprime p :=
    Nat.Coprime.prod_left fun i _ =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm
  have hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i ≤ P.natDegree
    · rcases hi.lt_or_eq with hlt | heq
      · obtain ⟨k, hk⟩ : (P.coeff i).den ∣ M :=
          Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
        have hc : P.coeff i * M = (P.coeff i).num * k := by
          rw [hk]
          push_cast
          rw [← _root_.mul_assoc, Rat.mul_den_eq_num]
        have hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        refine ⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩
        rw [hpow, ← _root_.mul_assoc, hc]
        simp
      · subst heq
        refine ⟨1, ?_⟩
        rw [Nat.sub_self, pow_zero, _root_.mul_one, map_one]
        exact (minpoly.monic hx).leadingCoeff.symm
    · refine ⟨0, ?_⟩
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
  have hmon : (P.scaleRoots (M : ℚ)).Monic := (Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon
  have hint : IsIntegral ℤ ((M : F) * x) := by
    refine ⟨Q, hQm, ?_⟩
    have h0 := Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)
    have hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast] at h0
    rw [← Polynomial.aeval_def]
    exact h0
  exact ⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩

theorem UpperTheory.Gal.W2.fInt_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FInt := by
  intro hE p _ G x hx
  apply integral_multiple_coprime
  apply coeff_den
  intro τ
  obtain ⟨w, σ, h | h⟩ := hE p G τ
  · rw [h x]
    calc ‖σ (G.emb w x)‖ = ‖G.emb w x‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).1
  · rw [h x]
    calc ‖σ (G.emb w ((IsCMField.complexConj G.F) x))‖
        = ‖G.emb w ((IsCMField.complexConj G.F) x)‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEmbAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.embAll_of :
    UpperTheory.Gal.W2.EmbAll := by
  intro p _ G τ
  rcases HTGroupOver.liesOver_or_conj p G τ with h | h
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ h
    refine ⟨i, σ, Or.inl fun x => ?_⟩
    rw [hσ]
    rfl
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ h
    refine ⟨i, σ, Or.inr fun x => ?_⟩
    have hx := congrArg (fun f : G.F →+* PadicAlgCl p => f (IsCMField.complexConj G.F x)) hσ
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      conjQ_apply] at hx
    have hc : (conjQ G.F).toRingHom ((IsCMField.complexConj G.F) x) = x := by
      simp [conjQ_apply]
    rw [hc] at hx
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFTrace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.FrobeniusTrace

variable {p : ℕ} [Fact p.Prime]

private theorem not_both (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (h1 : LiesOver G.Kq G.u τ)
    (h2 : LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))) : False := by
  obtain ⟨x, hx, hne⟩ := CentAtP.exists_conj_ne G
  apply hne
  apply τ.injective
  have a := h1 ⟨x, hx⟩
  have b := h2 ⟨x, hx⟩
  exact b.trans a.symm

private theorem exists_ext (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : E, σ (y : PadicAlgCl p) = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact congrArg (fun f => f y) hφ

private theorem hom_ext {F : Type} [Field F] (τ : F →+* PadicAlgCl p)
    (s s' : FwOf τ →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (embOf τ x) = s' (embOf τ x)) : s = s' := by
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p]
    (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

private theorem sigma_eq (G : HTGroup p) {w w' : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)
    (s' : G.Fw w' →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (G.embW w x) = s' (G.embW w' x)) :
    (⟨w, s⟩ : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) = ⟨w', s'⟩ := by
  obtain ⟨σ, hσ⟩ := exists_ext _ s
  obtain ⟨σ', hσ'⟩ := exists_ext _ s'
  have hw : w = w' := by
    refine G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)
    have e1 : σ (G.emb w x) = s (G.embW w x) := hσ (G.embW w x)
    have e2 : σ' (G.emb w' x) = s' (G.embW w' x) := hσ' (G.embW w' x)
    change σ'.symm (σ (G.emb w x)) = G.emb w' x
    rw [e1, h, ← e2, AlgEquiv.symm_apply_apply]
  subst hw
  rw [hom_ext (G.emb w) s s' h]

private theorem liesOver_comp (G : HTGroup p) {w : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    LiesOver G.Kq G.u ((s : G.Fw w →+* PadicAlgCl p).comp (G.embW w)) := by
  intro x
  have e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x) := Subtype.ext (G.emb_over w x)
  change s (G.embW w (x : G.F)) = _
  rw [e, s.commutes]

private noncomputable def phi (G : HTGroup p) :
    ((Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) ⊕ (Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) →
      (G.F →ₐ[ℚ] PadicAlgCl p)
  | .inl a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1)).toRatAlgHom
  | .inr a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp
      ((G.embW a.1).comp (IsCMField.complexConj G.F : G.F →+* G.F))).toRatAlgHom

private theorem phi_inl (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inl a) x = a.2 (G.embW a.1 x) := rfl

private theorem phi_inr (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inr a) x = a.2 (G.embW a.1 (IsCMField.complexConj G.F x)) := rfl

private theorem phi_ne (G : HTGroup p) (a b : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    phi G (.inl a) ≠ phi G (.inr b) := by
  intro h
  refine not_both G _ (liesOver_comp G a.2) fun k => ?_
  have e := DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))
  rw [phi_inl, phi_inr, IsCMField.complexConj_apply_apply] at e
  exact e.trans (liesOver_comp G b.2 k)

private theorem phi_injective (G : HTGroup p) : Function.Injective (phi G) := by
  rintro (⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab
  · rw [sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans
      ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]
  · exact absurd hab (phi_ne G _ _)
  · exact absurd hab.symm (phi_ne G _ _)
  · have key : ∀ y, s (G.embW w y) = s' (G.embW w' y) := by
      intro y
      have e := (phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans
        ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))
      rwa [IsCMField.complexConj_apply_apply] at e
    rw [sigma_eq G s s' key]

private theorem phi_surjective (hE : EmbAll) (G : HTGroup p) : Function.Surjective (phi G) := by
  intro ψ
  obtain ⟨w, σ, h | h⟩ := hE p G ψ.toRingHom
  · refine ⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inl]
    exact (h x).symm
  · refine ⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inr]
    exact (h x).symm

end UpperTheory.Gal.W2.FrobeniusTrace

open UpperTheory.Gal.W2.FrobeniusTrace in
theorem UpperTheory.Gal.W2.fTrace_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FTrace := by
  intro hE p _ G x
  apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  rw [map_add, map_sum, map_sum]
  have hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p])
      = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x) := by
    simp only [map_ratCast, eq_ratCast]
  rw [hl]
  simp_rw [trace_eq_sum_embeddings (E := PadicAlgCl p)]
  rw [← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩
    (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [phi_inl, phi_inr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKpMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocLat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def colM {K : Type*} {n : ℕ} (b : Fin n → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => b j i

private theorem colM_update {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K) (i : Fin n)
    (y : Fin n → K) : (colM b).updateCol i y = colM (Function.update b i y) := by
  ext r c
  by_cases h : c = i
  · subst h; simp [colM, Matrix.updateCol_apply]
  · simp [colM, Matrix.updateCol_apply, h, Function.update_of_ne]

private theorem colM_mulVec {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K)
    (c : Fin n → K) : colM b *ᵥ c = ∑ i, c i • b i := by
  ext r
  simp [colM, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private theorem exists_frame {K : Type*} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ b : Fin n → Fin n → K, (colM b).det ≠ 0 ∧ (∀ i, b i ∈ s) ∧
      ∀ y ∈ s, ∃ c : Fin n → K, (∀ i, f (c i) ≤ 1) ∧ colM b *ᵥ c = y := by
  classical
  have h1 : f 1 = 1 := by
    have h := hm 1 1
    have hp := hpos 1 one_ne_zero
    rw [_root_.one_mul] at h
    exact mul_left_cancel₀ hp.ne' (by rw [_root_.mul_one]; exact h.symm)
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (s : Set (Fin n → K))
  have hfin : t.Finite := s.finite_toSet.subset hts
  haveI := hfin.fintype
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : t → Fin n → K)) := by
    rw [Subtype.range_coe, hspan, hs]
  have hcard : Fintype.card t = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e := Fintype.equivFinOfCardEq hcard
  let b0 : Fin n → Fin n → K := fun i => (e.symm i).1
  have hb0 : (colM b0).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hd
    rw [colM_mulVec] at hMv
    have hli' : LinearIndependent K b0 := hli.comp e.symm e.symm.injective
    exact hv (funext (Fintype.linearIndependent_iff.mp hli' v hMv))
  let F : (Fin n → s) → ℝ := fun g => f (colM (fun i => (g i : Fin n → K))).det
  obtain ⟨g0, -, hg0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → s)) F
    ⟨fun i => ⟨b0 i, hts (e.symm i).2⟩, Finset.mem_univ _⟩
  let b : Fin n → Fin n → K := fun i => (g0 i : Fin n → K)
  have hle : F (fun i => ⟨b0 i, hts (e.symm i).2⟩) ≤ f (colM b).det := hg0 _ (Finset.mem_univ _)
  have hpos0 : 0 < f (colM b).det := lt_of_lt_of_le (hpos _ hb0) hle
  have hdet : (colM b).det ≠ 0 := by
    intro h
    rw [h, h0] at hpos0
    exact lt_irrefl _ hpos0
  refine ⟨b, hdet, fun i => (g0 i).2, ?_⟩
  intro y hy
  set d := (colM b).det with hd
  refine ⟨d⁻¹ • (colM b).cramer y, ?_, ?_⟩
  · intro i
    have hupd : Function.update b i y = fun j => ((Function.update g0 i ⟨y, hy⟩ j : s) : Fin n → K) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [b]
      · simp [b, Function.update_apply, hj]
    have hmax : f (colM (Function.update b i y)).det ≤ f d := by
      rw [hupd]
      exact hg0 _ (Finset.mem_univ _)
    have hinv : f d⁻¹ = (f d)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← hm, mul_inv_cancel₀ hdet, h1]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, colM_update]
    rw [hm, hinv, inv_mul_le_iff₀ hpos0, _root_.mul_one]
    exact hmax
  · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]

private theorem exists_gl {K : Type} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ g : GL (Fin n) K, ∀ z : Fin n → K,
      (∀ i, f ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) i) ≤ 1) ↔
        ∃ a : (Fin n → K) → K, (∀ y, f (a y) ≤ 1) ∧ z = ∑ y ∈ s, a y • y := by
  classical
  obtain ⟨b, hdet, hbs, hcoord⟩ := exists_frame f h0 hm hpos hnn ha s hs
  have hu : IsUnit (colM b) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨hu.unit, ?_⟩
  have hl : ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * colM b = 1 := by
    have h := Units.inv_mul hu.unit
    rwa [IsUnit.unit_spec] at h
  have hr : colM b * ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h := Units.mul_inv hu.unit
    rwa [IsUnit.unit_spec] at h
  have hsum : ∀ {α : Type} (t : Finset α) (u : α → K), (∀ i ∈ t, f (u i) ≤ 1) →
      f (∑ i ∈ t, u i) ≤ 1 := by
    intro α t u hu'
    exact Finset.sum_induction u (fun x => f x ≤ 1)
      (fun x y hx hy => (ha x y).trans (max_le hx hy)) (by rw [h0]; exact zero_le_one) hu'
  intro z
  constructor
  · intro hz
    set c := ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z with hc
    have hzc : z = colM b *ᵥ c := by
      rw [hc, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
    refine ⟨fun y => ∑ i, if b i = y then c i else 0, ?_, ?_⟩
    · intro y
      apply hsum
      intro i _
      split_ifs
      · exact hz i
      · rw [h0]
        exact zero_le_one
    · rw [hzc, colM_mulVec]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq, if_pos (hbs i)]
  · rintro ⟨a, ha1, rfl⟩ i
    choose! C hC1 hC2 using hcoord
    have hz : ∑ y ∈ s, a y • y = colM b *ᵥ ∑ y ∈ s, a y • C y := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Matrix.mulVec_smul, hC2 y hy]
    rw [hz, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply hsum
    intro y hy
    rw [hm]
    exact mul_le_one₀ (ha1 y) (hnn _) (hC1 y hy i)

theorem UpperTheory.Gal.W2.locLat_of :
    UpperTheory.Gal.W2.LocLat := by
  intro p _ G w s hs
  exact exists_gl (fun x : G.Fw w => ‖(x : PadicAlgCl p)‖) (by simp)
    (fun x y => by
      push_cast
      exact norm_mul _ _)
    (fun x hx => norm_pos_iff.mpr (by exact_mod_cast hx))
    (fun x => norm_nonneg _)
    (fun x y => by
      push_cast
      exact IsUltrametricDist.norm_add_le_max _ _) s hs
end

