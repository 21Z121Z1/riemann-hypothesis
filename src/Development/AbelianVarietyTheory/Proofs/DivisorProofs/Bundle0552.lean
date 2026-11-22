import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrime
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame.GramSchmidt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sum_left (G : Matrix (Fin r) (Fin r) E) (s : Finset (Fin r)) (f : Fin r → E)
    (w : Fin r → Fin r → E) (y : Fin r → E) :
    herm G (∑ j ∈ s, f j • w j) y = ∑ j ∈ s, f j * herm G (w j) y := by
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, ih]

theorem psi_nonempty (X : Data E r) : ∃ τ, τ ∈ X.Ψ := by
  let τ0 : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  by_cases h : τ0 ∈ X.Ψ
  · exact ⟨τ0, h⟩
  · exact ⟨_, not_not.mp (mt (X.cmType τ0).2 h)⟩

theorem dmin_frm_of_lt (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (i : Fin (r + 1))
    (ho : ∀ j k : Fin r, (j : ℕ) < i → (k : ℕ) < i → j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (by rw [Fin.coe_castLE]; exact a.isLt) (by rw [Fin.coe_castLE]; exact b.isLt)
        (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem herm_self_ne (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : ℕ)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (j : Fin r) (hj : (j : ℕ) < m) : herm X.Gm (v j) (v j) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := psi_nonempty X
  have h1 := (hv ⟨τ, hτ⟩).2 j.succ
  have hd : dmin X.Gm (frm X.Ψ v) ⟨τ, hτ⟩ j.succ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [dmin_frm_of_lt X.Ψ X.Gm v j.succ (fun a b ha hb hab => ho a b
    (by simp only [Fin.val_succ] at ha; omega) (by simp only [Fin.val_succ] at hb; omega) hab)] at hd
  have hf := Finset.prod_ne_zero_iff.mp hd ⟨j, by simp⟩ (Finset.mem_univ _)
  have he : (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) ⟨(j : ℕ), by simp⟩ : Fin r) = j := Fin.ext rfl
  rw [he] at hf
  intro h0
  exact hf (by rw [h0, map_zero])

def gsMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Matrix (Fin r) (Fin r) E :=
  fun j a => (if j = a then 1 else 0) -
    (if a = m ∧ j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0)

def gsStep (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Fin r → Fin r → E :=
  fun a k => ∑ j, v j k * gsMat G v m j a

theorem gsStep_ne (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m a : Fin r)
    (h : a ≠ m) : gsStep G v m a = v a := by
  funext k
  simp [gsStep, gsMat, h]

theorem gsStep_self (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    gsStep G v m m = v m - ∑ j, (if j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0) • v j := by
  funext k
  simp only [gsStep, gsMat, true_and, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem frm_gsStep (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : frm Ψ (gsStep G v m) = rmul (frm Ψ v) (fun τ j a => τ.1 (gsMat G v m j a)) := by
  funext τ k a
  simp [frm, rmul, mat, Matrix.mul_apply, gsStep, map_sum, map_mul]

theorem gsB_mem (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) ∈ Bor Ψ r := by
  have hlow : ∀ a c : Fin r, c < a → gsMat G v m a c = 0 := by
    intro a c hca
    have h1 : a ≠ c := fun h => lt_irrefl _ (h ▸ hca)
    have h2 : ¬ (c = m ∧ a < m) := fun h => lt_asymm hca (h.1 ▸ h.2)
    simp [gsMat, h1, h2]
  intro τ
  refine ⟨?_, fun a c hca => by simp [hlow a c hca]⟩
  have ht : (mat (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) τ).BlockTriangular id := by
    intro a c hca
    simp [mat, hlow a c hca]
  rw [Matrix.det_of_upperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have hn : ¬ (a = m ∧ a < m) := by rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [mat, gsMat, hn]

theorem herm_gsStep_self (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : Fin r)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (k : Fin r) (hk : k < m) : herm X.Gm (gsStep X.Gm v m m) (v k) = 0 := by
  have hkm : (k : ℕ) < m := hk
  have hne := herm_self_ne X v hv m ho k hkm
  rw [gsStep_self, HermitianTraceFormVanishing.herm_sub_left, herm_sum_left,
    Finset.sum_eq_single k (fun i _ hik => ?_) (fun h => absurd (Finset.mem_univ k) h),
    if_pos hk, div_mul_cancel₀ _ hne, sub_self]
  split_ifs with him
  · rw [ho i k him hkm hik, mul_zero]
  · rw [zero_mul]

theorem exists_ortho_lt (X : Data E r) (u : Fin r → Fin r → E) (hu : frm X.Ψ u ∈ X.dom) :
    ∀ m ≤ r, ∃ v : Fin r → Fin r → E, frm X.Ψ v ∈ X.dom ∧
      ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨u, hu, fun j k hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv, ho⟩ := ih (Nat.le_of_succ_le hm)
    let mf : Fin r := ⟨m, hm⟩
    refine ⟨gsStep X.Gm v mf, ?_, ?_⟩
    · rw [frm_gsStep]
      exact OrthogonalFrameDomain.rmul_mem_dom X hv (gsB_mem X.Ψ X.Gm v mf)
    · intro j k hj hk hjk
      by_cases hjm : j = mf
      · have hkm : k ≠ mf := fun h => hjk (hjm.trans h.symm)
        have hk' : k < mf := by
          rw [Fin.lt_iff_val_lt_val]
          have : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          show (k : ℕ) < m
          omega
        rw [hjm, gsStep_ne X.Gm v mf k hkm]
        exact herm_gsStep_self X v hv mf ho k hk'
      · by_cases hkm : k = mf
        · have hj' : j < mf := by
            rw [Fin.lt_iff_val_lt_val]
            have : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
            show (j : ℕ) < m
            omega
          rw [hkm, gsStep_ne X.Gm v mf j hjm, ← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm,
            herm_gsStep_self X v hv mf ho j hj', HermitianTraceFormVanishing.cc_zero]
        · rw [gsStep_ne X.Gm v mf j hjm, gsStep_ne X.Gm v mf k hkm]
          have hj' : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
          have hk' : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          exact ho j k (by omega) (by omega) hjk

theorem exists_ortho_frm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E) :
    GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E,
      (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  intro hu
  obtain ⟨v, hv, ho⟩ := exists_ortho_lt X u hu r le_rfl
  exact ⟨v, fun j k hjk => ho j k j.isLt k.isLt hjk, hv⟩

end

end GlobalTheory.OrthoFrame.GramSchmidt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZeroStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceUniformiserIdeleStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_uniformiser_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E), Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) → ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧ modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  first | exact @GlobalTheory.CMVal.Euler.exists_split_unif_idele | exact GlobalTheory.CMVal.Euler.exists_split_unif_idele | (intros; apply GlobalTheory.CMVal.Euler.exists_split_unif_idele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubring
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.TorsorUnionDescent

theorem exists_stage_torsor : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T _ _ ι _ _ _ 𝒜 hA hU q hq E _ _ _ _ _ Q _ D₁ _ _ act₁ htor
  obtain ⟨i₀, E₀, _, _, hE₀, ⟨iso₀⟩⟩ := GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union T ι 𝒜 hA hU E

  let ι' := {k : ι // i₀ ≤ k}
  haveI : IsDirected ι' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  haveI : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  let 𝒜' : ι' → Subring T := fun k => 𝒜 k.1
  have hA' : Monotone 𝒜' := fun a b hab => hA hab
  have hU' : ∀ x : T, ∃ k : ι', x ∈ 𝒜' k := fun x => by
    obtain ⟨j, hj⟩ := hU x
    obtain ⟨c, hjc, hic⟩ := directed_of (· ≤ ·) j i₀
    exact ⟨⟨c, hic⟩, hA hjc hj⟩
  obtain ⟨Ek, _, _, _, _, _, e, h, he, hh, heh, hid, hcomp, hinj, hsurj⟩ :=
    GlobalTheory.T.directedSystem_etale_baseChange_polynomial T ι' 𝒜' hA' hU' ⟨i₀, le_rfl⟩ (fun k => k.2) E E₀ ⟨iso₀⟩
  have he' : ∀ k (a : 𝒜' k), e k (algebraMap (𝒜' k) (Ek k) a) = algebraMap T E a := by
    intro k a
    have := congrArg (fun φ => φ (Polynomial.C a)) (he k)
    simpa [IsScalarTower.algebraMap_apply (𝒜' k) (Polynomial (𝒜' k)) (Ek k),
      IsScalarTower.algebraMap_apply T (Polynomial T) E] using this
  have hnz : ∀ (S S' : Subring T) (φ : S →+* S'), (∀ a, (φ a : T) = a) →
      ∀ a ∈ nonZeroDivisors S, φ a ∈ nonZeroDivisors S' := by
    intro S S' φ hφ a ha
    refine mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext ?_))
    have := congrArg Subtype.val h0
    rw [hφ] at this
    exact this
  have hnzT : ∀ (S : Subring T), ∀ a ∈ nonZeroDivisors S, S.subtype a ∈ nonZeroDivisors T := by
    intro S a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext h0))
  let g : ∀ k : ι', GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) := fun k =>
    GlobalTheory.GenFibMap.genFibMap (𝒜' k).subtype (e k) (he' k) (hnzT _) (Q.comap (e k)) Q rfl
  have hQ : ∀ k l (hkl : k ≤ l), Q.comap (e k) = (Q.comap (e l)).comap (h k l hkl) := by
    intro k l hkl
    rw [Ideal.comap_comap]
    congr 1
    ext y
    exact (heh k l hkl y).symm
  let f : ∀ k l : ι', k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))) := fun k l hkl =>
    GlobalTheory.GenFibMap.genFibMap (Subring.inclusion (hA' hkl)) (h k l hkl) (hh k l hkl)
      (hnz _ _ _ (fun _ => rfl)) (Q.comap (e k)) (Q.comap (e l)) (hQ k l hkl)
  have hgc : ∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y)) := fun k y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  have hfc : ∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y)) := fun k l hkl y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  obtain ⟨k, Di, _, _, acti, htori, ⟨iso₂⟩⟩ := GlobalTheory.T.exists_torsor_model_filtered_colimit ι'
    (fun k => GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) f
    (fun k hkk => GlobalTheory.GenFibMap.genFibMap_id _ _ _ _ _ _ (hid k hkk))
    (fun k l m hkl hlm => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hcomp k l m hkl hlm (hkl.trans hlm)))
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) g
    (fun k l hkl => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun y => (heh k l hkl y).symm))
    (GlobalTheory.T.genericFibreLocalization_directedUnion_surjective T ι' 𝒜' hA' hU' E Q Ek e h he' heh hsurj g hgc)
    (GlobalTheory.T.genericFibreLocalization_directedUnion_kernel T ι' 𝒜' hA' hU' E Q Ek e h he' hh heh hinj hsurj g hgc f hfc)
    q hq D₁ act₁ htor
  refine ⟨k.1, Ek k, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, e k, he k,
    g k, GlobalTheory.GenFibMap.genFibMap_comp_algebraMap _ _ _ _ _ _ _, Di, inferInstance, inferInstance, acti, htori, ?_⟩
  intro C _ ψ σ hσ
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
      (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := (g k).toAlgebra
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) C :=
    (ψ.comp (g k)).toAlgebra
  let ψa : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k)
      (Localization.AtPrime (Q.comap (e k)))] C := { ψ with commutes' := fun r => rfl }
  let σa : Di →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))] C :=
    { σ with commutes' := fun r => (congrArg (fun φ => φ r) hσ : _) }
  refine ⟨(Algebra.TensorProduct.lift ψa σa (fun _ _ => Commute.all _ _)).toRingHom.comp
    iso₂.symm.toAlgHom.toRingHom, ?_⟩
  ext b
  simp [ψa]

end GlobalTheory.TorsorUnionDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOne
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusAngles

theorem exp_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at h
  simpa [mul_comm] using h

theorem exp_neg_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (-(Complex.I * (Complex.arg w : ℂ))) = w⁻¹ := by
  rw [Complex.exp_neg, exp_I_arg hw]

theorem exists_angles_of_prod_eq_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 →
    ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  intro r z hz hp
  rcases r with _ | n
  · exact ⟨fun _ => 0, fun a => a.elim0⟩
  · refine ⟨fun k => Complex.arg (z ⟨k, by omega⟩), fun a => ?_⟩
    unfold angles
    split_ifs with h
    · exact exp_I_arg (hz _)
    · have ha : a = Fin.last n := by ext; simp at h ⊢; omega
      subst ha
      rw [Fin.prod_univ_castSucc] at hp
      have hlast : z (Fin.last n) = (∏ k : Fin n, z k.castSucc)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right hp
      rw [hlast, Complex.ofReal_neg, Complex.ofReal_sum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
        Complex.exp_sum, ← Finset.prod_inv_distrib]
      show ∏ k : Fin n, Complex.exp (-(Complex.I * (Complex.arg (z ⟨k, _⟩) : ℂ))) = _
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [exp_neg_I_arg (hz _)]
      rfl

end GlobalTheory.TorusAngles
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserSplitPlaceCmOrderNonunitStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_split_place_cm_order_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  first | exact @GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff | exact GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff | (intros; apply GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminantStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_with_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (u : E), 0 < r → (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 → u * IsCMField.complexConj E u = 1 → ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (γ : Matrix (Fin r) (Fin r) E).det = u := by
  first | exact @GlobalTheory.UnitDet.main | exact GlobalTheory.UnitDet.main | (intros; apply GlobalTheory.UnitDet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrime
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSmoothOfSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_smooth_of_section' : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  first | exact @GlobalTheory.geometricallyConnected_of_smooth_of_section | exact GlobalTheory.geometricallyConnected_of_smooth_of_section | (intros; apply GlobalTheory.geometricallyConnected_of_smooth_of_section <;> assumption)
end

