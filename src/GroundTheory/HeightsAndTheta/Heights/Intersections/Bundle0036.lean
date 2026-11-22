import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem PFSecRed.exists_form_not_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s c ∧ s ∉ P :=
  ⟨∏ k, (X ⟨k, (hP.2.1.2.2 k).choose⟩ : MRing ι) ^ c k, AvoidRing.isMultiHomog_coordProd _ c,
    AvoidRing.coordProd_not_mem hP.2.1.1 _ (fun k => (hP.2.1.2.2 k).choose_spec) c⟩

theorem PFSecRed.proof
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      MultilinStatement F ι)
    (hDim : FibreDimStatement) : PFSecRed.Statement := by
  intro I hI r hsec K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' hN

  let c : K' → ℕ := fun k => (-(N (Fin.last r)).a k).toNat
  let H : HermLine ι' := HermLine.sqMetric c
  let A : HermLine ι' := (N (Fin.last r)).tensor H
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric c
  have hAs : IsSmoothHerm A := isSmoothHerm_tensor (hN _) hHs
  let a : K' → ℕ := fun k => ((N (Fin.last r)).a k + c k).toNat
  have hAa : ∀ k, A.a k = a k := by
    intro k
    show (N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ) =
      (((N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ)).toNat : ℤ)
    omega
  have hHa : ∀ k, H.a k = c k := fun k => rfl
  obtain ⟨sA, hsA, hsAP⟩ := PFSecRed.exists_form_not_mem hP' a
  obtain ⟨sH, hsH, hsHP⟩ := PFSecRed.exists_form_not_mem hP' c
  have hsnoc : ∀ B : HermLine ι', IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc (Fin.init N) B : Fin (r + 1) → HermLine ι') j) := by
    intro B hB j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hB
    · rw [Fin.snoc_castSucc]; exact hN _
  have e1 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) A) sA a hv hP' hP hJ hL hL'
    (hsnoc A hAs) (by simpa using hAa) hsA hsAP
  have e2 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) H) sH c hv hP' hP hJ hL hL'
    (hsnoc H hHs) (by simpa using hHa) hsH hsHP

  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact IsPullHerm.isSmoothHerm hv (hL' i) (hL i)
    | right i => rw [Fin.append_right]; exact hN _
  have hadd := (hI K' ι').2.1 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) H hP' hM (hN _) hHs
  rw [← Fin.append_snoc, ← Fin.append_snoc, ← Fin.append_snoc, Fin.snoc_init_self] at hadd

  have hV := hDim K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hJadd := hMult G.Φ (FibreBlock κ) (fibreIdx ι' κ) J hJ (fibreIdeal κ G) (r + 1)
    (Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a)) (Fin.last r)
    (fibreDeg κ (N (Fin.last r)).a) (fibreDeg κ H.a) hV
  simp only [Fin.update_snoc_last] at hJadd
  have f0 : (fun j => fibreDeg κ (N j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  have f1 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) A : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a + fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp [Fin.init]
  have f2 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) H : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Fin.init]
  rw [f1] at e1
  rw [f2] at e2
  have key : I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) A)) -
        I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) H)) := by
    rw [eq_sub_iff_add_eq]
    exact hadd.symm
  rw [f0, key, e1, e2, hJadd]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section LinSubst

variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

def linSubst (ℓ : σ → Fin n → Φ) : MvPolynomial σ Φ →ₐ[Φ] MvPolynomial (Fin n) Φ :=
  aeval fun q => ∑ a, C (ℓ q a) * X a

def linKerForms (ℓ : σ → Fin n → Φ) : Set (MvPolynomial σ Φ) :=
  {f | ∃ μ : σ → Φ, (∀ b, ∑ q, μ q * ℓ q b = 0) ∧ f = ∑ q, C (μ q) * X q}

theorem sum_C_mul_linForm {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, mul_assoc]

theorem linSubst_linForm (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by
  rw [← sum_C_mul_linForm μ ℓ]
  simp only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]

theorem ker_linSubst (ℓ : σ → Fin n → Φ) (ν : Fin n → σ → Φ)
    (hν : ∀ a b, ∑ q, ν a q * ℓ q b = if a = b then 1 else 0) :
    RingHom.ker (linSubst ℓ) = Ideal.span (linKerForms ℓ) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · set I := Ideal.span (linKerForms ℓ)
    let ρ : MvPolynomial (Fin n) Φ →ₐ[Φ] MvPolynomial σ Φ ⧸ I :=
      aeval fun a => Ideal.Quotient.mk I (∑ q, C (ν a q) * X q)
    have hρ : ρ.comp (linSubst ℓ) = Ideal.Quotient.mkₐ Φ I := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      have h1 : ρ (linSubst ℓ (X q)) =
          Ideal.Quotient.mk I (∑ q', C (∑ a, ℓ q a * ν a q') * X q') := by
        rw [← sum_C_mul_linForm]
        simp only [ρ, linSubst, aeval_X, map_sum, map_mul, aeval_C]
        rfl
      rw [h1, Ideal.Quotient.eq]
      refine Ideal.subset_span ⟨fun q' => ∑ a, ℓ q a * ν a q' - if q' = q then 1 else 0, fun b => ?_, ?_⟩
      · simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hν, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp
      · simp [sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]
    have h2 := congrArg (fun φ => φ f) hρ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [RingHom.mem_ker] at hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h2]
    erw [hf]
    exact map_zero ρ
  · rw [Ideal.span_le]
    rintro f ⟨μ, hμ, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    erw [linSubst_linForm]
    simp [hμ]

end LinSubst

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_genPt_eq_mk (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) := by
  have h : (aeval (genPt P) : MRing ι →ₐ[ℤ] FnField P).toRingHom =
      (algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [genPt])
  exact RingHom.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem projBundleMap_X_inr (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (u : Unit) (j : Fin N1) :
    projBundleMap P B (X ⟨Sum.inr u, j⟩) = ∑ a, C (B a j) * X a := by
  simp [projBundleMap]

def projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (Σ k, PBlk ι N1 k) → FractionRing (MvPolynomial (Fin n) (FnField P)) :=
  fun p => algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B (X p))

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_projBundlePt (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) {_ : Algebra ℤ (FractionRing (MvPolynomial (Fin n) (FnField P)))}
    (f : MRing (PBlk ι N1)) :
    aeval (projBundlePt P B) f = algebraMap (MvPolynomial (Fin n) (FnField P)) _ (projBundleMap P B f) := by
  have h : (aeval (projBundlePt P B) : MRing (PBlk ι N1) →ₐ[ℤ] _).toRingHom =
      (algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
        (projBundleMap P B) :=
    MvPolynomial.ringHom_ext (fun r => by rw [show (C r : MvPolynomial _ ℤ) = (r : MvPolynomial _ ℤ) from
      eq_intCast C r, map_intCast, map_intCast])
      (fun p => by simp [projBundlePt])
  exact RingHom.congr_fun h f

def projBundleGenFibre (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) where
  Φ := FnField P
  Φ' := FractionRing (MvPolynomial (Fin n) (FnField P))
  x := genPt P
  x' := projBundlePt P B
  ker_x := by
    rw [imageZ_projBundleIdeal]
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_genPt_eq_mk P f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans Ideal.Quotient.eq_zero_iff_mem)
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · exact fun h => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb ((aeval_genPt_eq_mk P g).symm.trans h)
    · exact (congrArg₂ (· / ·) (aeval_genPt_eq_mk P f) (aeval_genPt_eq_mk P g)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker]
    exact (Eq.congr_left (aeval_projBundlePt P B f)).trans
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)
  compat p := by
    obtain ⟨k, i⟩ := p
    simp [projBundlePt, inlV, projBundleMap, IsScalarTower.algebraMap_apply (FnField P)
      (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))]

end Main

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem fibreBlock_inl_subsingleton (k k' : FibreBlock (Sum.inl : K → K ⊕ Unit)) : k = k' := by
  rcases k with ⟨k | u, hk⟩
  · exact absurd ⟨k, rfl⟩ hk
  rcases k' with ⟨k' | u', hk'⟩
  · exact absurd ⟨k', rfl⟩ hk'
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

def fibreCoordEquiv (ι : K → Type) (N1 : ℕ) :
    (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) ≃ Fin N1 where
  toFun
    | ⟨⟨.inl k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨.inr _, _⟩, j⟩ => j
  invFun j := ⟨⟨.inr (), by rintro ⟨k, hk⟩; cases hk⟩, j⟩
  left_inv := by
    rintro ⟨⟨k | u, h⟩, j⟩
    · exact absurd ⟨k, rfl⟩ h
    · rfl
  right_inv _ := rfl

theorem isMultiHomog_linForm {Φ : Type} [Field Φ] {N1 : ℕ}
    (μ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Φ) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver Φ (fibreIdx (PBlk ι N1) Sum.inl)) fun _ => 1 := by
  classical
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_inl_subsingleton _ _
  simp [Finsupp.single_apply]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem fibreIdeal_projBundleGenFibre (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (projBundleGenFibre P B) =
      RingHom.ker (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
  have h : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
      projBundlePt P B ⟨q.1.1, q.2⟩) f =
      algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))
        (linSubst (fun q a => B a (fibreCoordEquiv ι N1 q)) f) := by
    intro f
    have e : (aeval fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
        projBundlePt P B ⟨q.1.1, q.2⟩) =
        (IsScalarTower.toAlgHom (FnField P) (MvPolynomial (Fin n) (FnField P))
          (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
          (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rcases q with ⟨⟨k | u, hk⟩, j⟩
      · exact absurd ⟨k, rfl⟩ hk
      · simp only [aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', linSubst, projBundlePt]
        exact congrArg _ (projBundleMap_X_inr P B u j)
    rw [e, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  ext f
  rw [fibreIdeal, RingHom.mem_ker]
  exact (Eq.congr_left (h f)).trans
    ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)

end Fibre

theorem ProjBundleFibreLine.proof : ProjBundleFibreLine.Statement := by
  intro K _ ι _ N1 t P d c m B hP _ hB
  have : P.IsPrime := hP.2.1.1
  classical
  set e := fibreCoordEquiv ι N1
  set ℓ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Fin 2 → FnField P :=
    fun q a => B a (e q) with hℓ
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FnField P) B).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hB.1.fintypeLinearCombination_injective)
  have hν : ∀ a b, ∑ q, g (Pi.single (e q) 1) a * ℓ q b = if a = b then 1 else 0 := by
    intro a b
    have h1 : ∑ q, g (Pi.single (e q) 1) a * ℓ q b = g (B b) a := by
      rw [Fintype.sum_equiv e (fun q => g (Pi.single (e q) 1) a * ℓ q b)
        (fun j => g (Pi.single j 1) a * B b j) (fun q => rfl)]
      have hB' : B b = ∑ j, B b j • Pi.single j (1 : FnField P) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hB']
      rw [map_sum, Finset.sum_apply]
      simp [mul_comm]
    have h2 : B b = Fintype.linearCombination (FnField P) B (Pi.single b 1) := by
      exact ((Fintype.linearCombination_apply_single (FnField P) B b (1 : FnField P)).trans (one_smul _ _)).symm
    rw [h1, h2, ← LinearMap.comp_apply, hg, LinearMap.id_apply, Pi.single_apply]
  refine ⟨projBundleGenFibre P B, linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_linForm μ
  · rw [fibreIdeal_projBundleGenFibre, ker_linSubst ℓ (fun a q => g (Pi.single (e q) 1) a) hν]
    exact rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace RatioAlgebraicDependence

variable {K : Type} {ι : K → Type} {d : ℕ}

def homog (c : ∀ k, ι k) (p : Fin d → Σ k, ι k) (f : MvPolynomial (Fin d) ℤ) : MvPolynomial (Σ k, ι k) ℤ :=
  ∑ m ∈ f.support, C (coeff m f) *
    ∏ j, X (p j) ^ m j * X ⟨(p j).1, c (p j).1⟩ ^ (f.totalDegree - m j)

theorem aeval_homog {F : Type} [Field F] [Algebra ℤ F] (c : ∀ k, ι k) (p : Fin d → Σ k, ι k)
    (f : MvPolynomial (Fin d) ℤ) (w : (Σ k, ι k) → F) (hw : ∀ j, w ⟨(p j).1, c (p j).1⟩ ≠ 0) :
    aeval w (homog c p f) = (∏ j, w ⟨(p j).1, c (p j).1⟩) ^ f.totalDegree *
      aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f := by
  classical
  have hsum : aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f =
      ∑ m ∈ f.support, aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [hsum, Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ j, m j ≤ f.totalDegree := fun j ↦
    (monomial_le_degreeOf j hm).trans (degreeOf_le_totalDegree f j)
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle j)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨(p j).1, c (p j).1⟩ ^ m j), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw j)),
    mul_comm]

end RatioAlgebraicDependence

open RatioAlgebraicDependence in

theorem RatioAlgDep.proof : RatioAlgDep.Statement := by
  intro K _ ι _ Q d c p hQ
  classical
  by_cases hX : ∃ k, (X ⟨k, c k⟩ : MRing ι) ∈ Q
  · obtain ⟨k, hk⟩ := hX
    refine ⟨1, one_ne_zero, fun z hz hzc ↦ absurd ?_ (hzc k)⟩
    simpa using hz _ hk
  push Not at hX
  obtain ⟨Ω, _, y, hy, hbir⟩ := HilbertSamuel.BirationalModelExists.proof K ι Q d hQ
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 ↦ hX k (by
    rw [← hy, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hQ
  have htr := ConeTrdeg.proof K ι Ω y hbir (fun k ↦ ⟨c k, hc k⟩) (hy ▸ hhor)
  rw [hy] at htr
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ Q) (CoordinateConeArithVar.algebraMap_injective Q hhor)
  rw [hdim, htr, map_add, map_natCast] at hA
  have hA' : ((d + Fintype.card K : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K + 1 := by exact_mod_cast hA
  have hlt : Algebra.trdeg ℤ Ω < d := by
    rw [← Cardinal.toENat_lt_natCast]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = n := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [hn] at hA' ⊢
    have : d + Fintype.card K = n + Fintype.card K + 1 := by exact_mod_cast hA'
    exact_mod_cast (by omega : n < d)
  have hdep : ¬ AlgebraicIndependent ℤ (fun j : Fin d ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) :=
    fun hind ↦ by
      have h := hind.cardinalMk_le_trdeg
      rw [Cardinal.mk_fin] at h
      exact absurd hlt (not_lt.2 h)
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨f, hf0, hfne⟩ := hdep

  have hH : homog c p f ∈ Q := by
    rw [← hy, mCoordIdeal, RingHom.mem_ker]
    set L := FractionRing (MvPolynomial K Ω)
    let φ : MvPolynomial K Ω →ₐ[ℤ] L :=
      { algebraMap (MvPolynomial K Ω) L with
        commutes' := fun n ↦ by simp }
    have hφ : Function.Injective φ := fun a b h ↦ IsFractionRing.injective (MvPolynomial K Ω) L h
    have hw : ∀ q : Σ k, ι k, y q ≠ 0 → φ (C (y q) * X q.1) ≠ 0 := fun q hq ↦ by
      rw [Ne, ← map_zero φ, hφ.eq_iff]
      exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)
    have hrat : ∀ j, φ (C (y (p j)) * X (p j).1) / φ (C (y ⟨(p j).1, c (p j).1⟩) * X (p j).1) =
        φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩)) := fun j ↦ by
      rw [div_eq_iff (hw _ (hc _)), ← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc _)]
    refine hφ ?_
    rw [map_zero, mConeMap, comp_aeval_apply, aeval_homog c p f _ (fun j ↦ hw _ (hc _))]
    simp only [hrat]
    let ψ : Ω →ₐ[ℤ] L := φ.comp (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω))
    have key : (aeval fun j ↦ φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩))) f =
        ψ (aeval (fun j ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) f) := by
      rw [comp_aeval_apply]
      rfl
    rw [key, hf0, map_zero, mul_zero]
  refine ⟨f, hfne, fun z hz hzc ↦ ?_⟩
  have h1 := hz _ hH
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_homog c p f z (fun j ↦ hzc _)] at h1
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact (mul_eq_zero.1 h1).resolve_left
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ hzc _))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

open Classical in

def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩

def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W

end Fibre

def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

end

end GroundTheory.Heights₂.Heights.Inter
end

