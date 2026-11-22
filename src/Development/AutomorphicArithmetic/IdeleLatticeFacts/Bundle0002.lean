import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsLocalLatticeOfGlobalLattice
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem ev_pair (P : HeightOneSpectrum (𝓞 E)) (α : Af F) :
    ev F E P (algebraMap (AF F) (AEF F E) (pairA F 0 α)) =
      GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) := by
  rw [ev_alg]
  rfl

private theorem ev_finIdem (P : HeightOneSpectrum (𝓞 E)) : ev F E P (finIdem F E) = 1 := by
  rw [finIdem, ev_pair, map_one, map_one]

private theorem finPart_lift (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem int_mem (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    algebraMap E (P.adicCompletion E) (r : E) ∈ P.adicCompletionIntegers E := by
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers P r

private theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (c : P.adicCompletionIntegers E) :
    ∃ a : AEF F E, finPartF F E a ∈ PositivityTheory.ThKW.LatB.hatO (F := F) E ∧ ev F E P a = c := by
  classical
  have hx : ∀ᶠ Q in Filter.cofinite, Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ (Q.adicCompletionIntegers E : Set (Q.adicCompletion E)) := by
    refine Filter.Eventually.of_forall fun Q => ?_
    by_cases h : Q = P
    · subst h
      rw [Pi.single_eq_same]
      exact c.2
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  let x : FiniteAdeleRing (𝓞 E) E := ⟨_, hx⟩
  have hxQ : ∀ Q, x Q ∈ Q.adicCompletionIntegers E := by
    intro Q
    by_cases h : Q = P
    · subst h
      show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) Q (c : Q.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_same]
      exact c.2
    · show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) Q ∈ _
      rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  refine ⟨PositivityTheory.ThKW.LatB.liftF F E ((finAdEquiv F E).symm x), ?_, ?_⟩
  · rw [finPart_lift]
    show _ ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))
    rw [← GlobalTheory.HeckeSplitGen.integralFiniteAdelesTensor_eq_adelicCompletion_integers]
    refine (mem_int_iff _).2 fun Q => ?_
    rw [RingEquiv.apply_symm_apply]
    exact hxQ Q
  · show evalV E P (finAdEquiv F E (finPartF F E _)) = c
    rw [finPart_lift, RingEquiv.apply_symm_apply]
    show Pi.single (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (c : P.adicCompletion E) P = c
    rw [Pi.single_eq_same]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

private theorem map_smul_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (M : Matrix (Fin nT) (Fin nS) E) :
    (r • M).map (algebraMap E (P.adicCompletion E)) =
      (⟨algebraMap E (P.adicCompletion E) (r : E), int_mem P r⟩ : P.adicCompletionIntegers E) •
        M.map (algebraMap E (P.adicCompletion E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

private theorem ev_map_smul (P : HeightOneSpectrum (𝓞 E)) (a : AEF F E) (z : WOF F E nS nT) :
    (a • z).map (ev F E P) = ev F E P a • z.map (ev F E P) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private theorem ev_ratWF (P : HeightOneSpectrum (𝓞 E)) (γ : Matrix (Fin nT) (Fin nS) E) :
    (ratWF (F := F) γ).map (ev F E P) = γ.map (algebraMap E (P.adicCompletion E)) := by
  refine Matrix.ext fun i j => ?_
  simp only [ratWF, Matrix.map_apply]
  exact ev_inc (F := F) P (γ i j)

private theorem finRat_mem (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) {M : Matrix (Fin nT) (Fin nS) E}
    (hM : M ∈ Λ) : finRatF F M ∈ latF F E nS nT Λ := by
  refine AddSubgroup.subset_closure ⟨1, ?_, M, hM, rfl⟩
  intro v
  rw [map_one]
  exact one_mem _

private theorem ev_finRat (P : HeightOneSpectrum (𝓞 E)) (M : Matrix (Fin nT) (Fin nS) E) :
    ((finRatF F M : XFF F E nS nT) : WOF F E nS nT).map (ev F E P) = M.map (algebraMap E (P.adicCompletion E)) := by
  show (finIdem F E • ratWF (F := F) M).map (ev F E P) = _
  rw [ev_map_smul, ev_finIdem, one_smul, ev_ratWF]

private theorem ev_mem_span (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    {z : WOF F E nS nT} (hz : z ∈ latOF F E nS nT Λ) :
    z.map (ev F E P) ∈ Submodule.span (P.adicCompletionIntegers E)
      {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))} := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hz
    rw [ev_map_smul, ev_pair, ev_ratWF]
    have hc : GlobalTheory.LFun.complMap rfl (evalV F (P.under (𝓞 F)) α) ∈ P.adicCompletionIntegers E :=
      GlobalTheory.LFun.complMap_mem rfl (hα _)
    exact Submodule.smul_mem _ (⟨_, hc⟩ : P.adicCompletionIntegers E) (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _)]
    exact neg_mem hx

end Aux2

theorem UpperTheory.exists_local_lattice_of_global_lattice :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
        (P : HeightOneSpectrum (𝓞 E)) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)), GoodLat Λ →
        ∃ L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          L.FG ∧ Submodule.span (P.adicCompletion E) (L : Set (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))) = ⊤ ∧
          ∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v := by
  intro F E _ _ _ _ _ nS nT P Λ hΛ
  classical
  refine ⟨Submodule.span (P.adicCompletionIntegers E)
    {X | ∃ M ∈ Λ, X = M.map (algebraMap E (P.adicCompletion E))}, ?_, ?_, ?_⟩
  · obtain ⟨G, hG⟩ := hΛ.fg
    refine ⟨G.image (fun M => M.map (algebraMap E (P.adicCompletion E))), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      have hM' : M ∈ Λ := by
        rw [← hG]
        exact Submodule.subset_span hM
      exact Submodule.subset_span ⟨M, hM', rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨M, hM, rfl⟩
      rw [← hG] at hM
      induction hM using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        rw [Matrix.map_zero _ (map_zero _)]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [Matrix.map_add _ (map_add _)]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul_int P r x]
        exact Submodule.smul_mem _ _ hx
  · rw [eq_top_iff]
    rintro X -
    rw [Matrix.matrix_eq_sum_single X]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨N, hN, hNM⟩ := hΛ.den (Matrix.single i j (1 : E))
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have key : Matrix.single i j (X i j) =
        (X i j * algebraMap E (P.adicCompletion E) (N : E)⁻¹) •
          (N • Matrix.single i j (1 : E)).map (algebraMap E (P.adicCompletion E)) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with h
      · rw [nsmul_eq_mul, mul_one, mul_assoc, ← map_mul, inv_mul_cancel₀ hN0, map_one, mul_one]
      · rw [smul_zero, map_zero, mul_zero]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨_, hNM, rfl⟩))
  · intro v
    constructor
    · intro hv
      induction hv using Submodule.span_induction with
      | mem X hX =>
        obtain ⟨M, hM, rfl⟩ := hX
        exact ⟨finRatF F M, finRat_mem Λ hM, ev_finRat P M⟩
      | zero =>
        refine ⟨0, zero_mem _, ?_⟩
        show (0 : WOF F E nS nT).map (ev F E P) = 0
        exact Matrix.map_zero _ (map_zero _)
      | add X Y _ _ hX hY =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨y, hy, rfl⟩ := hY
        refine ⟨x + y, add_mem hx hy, ?_⟩
        show ((x : WOF F E nS nT) + (y : WOF F E nS nT)).map (ev F E P) = _
        exact Matrix.map_add _ (map_add _) _ _
      | smul c X _ hX =>
        obtain ⟨x, hx, rfl⟩ := hX
        obtain ⟨a, ha, hac⟩ := exists_lift (F := F) P c
        refine ⟨a • x, PositivityTheory.ThKW.LatB.int_smul_mem ha hx, ?_⟩
        rw [GlobalTheory.FinLatF.XFF.coe_asmul, ev_map_smul, hac]
        rfl
    · rintro ⟨x, hx, rfl⟩
      exact ev_mem_span P Λ hx
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsSignHeckeCharAtNonfixedPlace
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem exists_unit {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ u : (FiniteAdeleRing (𝓞 E) E)ˣ, Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = WithZero.exp (-1 : ℤ) ∧
      ∀ Q, Q ≠ P → (u : FiniteAdeleRing (𝓞 E) E) Q = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E P
  have hv : Valued.v (algebraMap E (P.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P π).trans hπ
  have h0 : algebraMap E (P.adicCompletion E) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let x : (P.adicCompletion E)ˣ := Units.mk0 _ h0
  refine ⟨Units.map (RingHom.snd _ _).toMonoidHom (Neutral.B1.localIdele E P x), ?_, fun Q hQ => ?_⟩
  · show Valued.v (((Neutral.B1.localIdele E P x : _) : AdeleRing (𝓞 E) E).2 P) = _
    rw [Neutral.B1.localIdele_snd_self]
    exact hv
  · exact (Neutral.B1.localIdele_isSupportedAt E P x).2 Q hQ

private theorem fin_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem inf_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : infPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => exact TensorProduct.zero_tmul _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

private theorem exists_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ z : (AEF F E)ˣ, wv F E P z = WithZero.exp (-1 : ℤ) ∧ ∀ Q, Q ≠ P → wv F E Q z = 1 := by
  obtain ⟨u, hu1, hu2⟩ := exists_unit P
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (u : FiniteAdeleRing (𝓞 E) E)
  obtain ⟨b, hb⟩ := (finAdEquiv F E).surjective ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
  have hab : a * b = 1 := (finAdEquiv F E).injective (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  have key : (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) * (PositivityTheory.ThKW.LatB.liftF F E b + (1 - finIdem F E)) = 1 := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · simp only [map_sub, map_mul, map_add, map_one, inf_lift, infPartF_finIdem, zero_add, sub_zero, mul_one, sub_self, map_zero]
    · simp only [map_sub, map_mul, map_add, map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero, hab, map_zero]
  let z : (AEF F E)ˣ := ⟨_, _, key, by rw [mul_comm]; exact key⟩
  have hev : ∀ Q, ev F E Q (z : AEF F E) = (u : FiniteAdeleRing (𝓞 E) E) Q := by
    intro Q
    have h1 : finPartF F E (z : AEF F E) = a := by
      show finPartF F E (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) = a
      rw [map_add, map_sub, map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero]
    show evalV E Q (finAdEquiv F E (finPartF F E (z : AEF F E))) = _
    rw [h1, ha]
    rfl
  refine ⟨z, ?_, fun Q hQ => ?_⟩
  · rw [wv_apply, hev, hu1]
  · rw [wv_apply, hev, hu2 Q hQ, map_one]

theorem UpperTheory.exists_sign_heckeChar_at_nonfixed_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (lam : ℕ →* ℂ)
        (κ : (AEF F E)ˣ →* Circle), IsKap σ lam κ → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx σ P →
        ∃ s : Circle, s * s = 1 ∧ lam (Ideal.absNorm P.asIdeal) = (s : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ∧
          ∀ (x : (AEF F E)ˣ) (m : ℤ), (∀ Q, Q ≠ P → wv F E Q x = 1) → wv F E P x = WithZero.exp m → κ x = s ^ m := by
  intro F E _ _ _ _ _ σ lam κ hκ P hP
  obtain ⟨z, hz1, hz2⟩ := exists_idele F E P
  refine ⟨κ z, hκ.sq z, hκ.gen P hP z hz1 hz2, fun x m hx1 hx2 => ?_⟩
  have hpow : ∀ Q, wv F E Q (z ^ m) = wv F E Q z ^ m := fun Q =>
    map_zpow' (wv F E Q) (fun y => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])) z m
  have h1 : κ (x * z ^ m) = 1 := by
    refine hκ.ker _ fun Q _ => ?_
    by_cases hQ : Q = P
    · subst hQ
      rw [map_mul, hpow, hx2, hz1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [map_mul, hpow, hx1 Q hQ, hz2 Q hQ, _root_.one_zpow, one_mul]
  rw [map_mul, map_zpow] at h1
  have h2 : κ z ^ m * κ z ^ m = 1 := by
    rw [← mul_zpow, hκ.sq z, _root_.one_zpow]
  exact mul_right_cancel (h1.trans h2.symm)
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.LatticeDeterminantComparisonAtSplitPlace
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem relIndex_map_of_injOn {G G' : Type} [AddGroup G] [AddGroup G'] (f : G →+ G') (R H K : AddSubgroup G)
    (hH : H ≤ R) (hK : K ≤ R) (hf : ∀ x ∈ R, f x = 0 → x = 0) :
    (H.map f).relIndex (K.map f) = H.relIndex K := by
  have hinj : Function.Injective (f.comp R.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have h1 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) hinj
  have h2 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) R.subtype_injective
  rw [AddSubgroup.map_addSubgroupOf_eq_of_le hH, AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h2
  rw [← AddSubgroup.map_map, ← AddSubgroup.map_map, AddSubgroup.map_addSubgroupOf_eq_of_le hH,
    AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h1
  exact h1.trans h2.symm

theorem UpperTheory.lattice_determinant_comparison_at_split_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
        (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (e : AEF F E), e * e = e →
        ∀ (P : HeightOneSpectrum (𝓞 E)), ev F E P e = 1 → (∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0) →
        ∀ (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
          (L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))),
          (∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v) →
        ∀ (g : GAF σ JS) (h : GAF σ JT)
          (T : Matrix (Fin nT) (Fin nS) (P.adicCompletion E) →ₗ[P.adicCompletion E] Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          (∀ u, T u = (mtF σ JT h).map (ev F E P) * u * (mtF σ JS g⁻¹).map (ev F E P)) →
          idx ((latF F E nS nT Λ).map (mulFF e)) (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) =
            idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) ∧
          idx (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) ((latF F E nS nT Λ).map (mulFF e)) =
            idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L := by
  intro F E _ _ _ _ _ σ nS nT JS JT e he P hev hinj Λ L hL g h T hT
  let φ : XFF F E nS nT →+ Matrix (Fin nT) (Fin nS) (P.adicCompletion E) :=
    AddMonoidHom.mk' (fun x => (x : WOF F E nS nT).map (ev F E P)) (fun x y => by
      rw [XFF.coe_add]
      ext i j
      simp [Matrix.map_apply, map_add])
  have hφ : ∀ x, φ x = (x : WOF F E nS nT).map (ev F E P) := fun _ => rfl
  have hφe : ∀ x, φ (mulFF e x) = φ x := by
    intro x
    rw [hφ, hφ, coe_mulFF]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hev]
  have hφr : ∀ x, φ (rhoFF σ JS JT (g, h) x) = T (φ x) := by
    intro x
    rw [hT, hφ, hφ, coe_rhoFF]
    show ((mtF σ JT h * (x : WOF F E nS nT)) * mtF σ JS g⁻¹).map (ev F E P) = _
    rw [Matrix.map_mul, Matrix.map_mul]
  let R : AddSubgroup (XFF F E nS nT) :=
    (LinearMap.range (mulFF e : XFF F E nS nT →ₗ[𝓞 E] XFF F E nS nT)).toAddSubgroup
  have hR : ∀ x ∈ R, φ x = 0 → x = 0 := by
    rintro _ ⟨y, rfl⟩ h0
    apply XFF.ext
    rw [XFF.coe_zero]
    ext i j
    apply hinj
    · rw [coe_mulFF]
      simp [Matrix.smul_apply, ← mul_assoc, he]
    · exact congrFun (congrFun h0 i) j
  have hmapA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup.map φ = L.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    rw [hL]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hφe x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hφe x⟩
  have hmapB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup.map φ =
      (L.map (T.restrictScalars (P.adicCompletionIntegers E))).toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      refine ⟨φ x, (hL _).2 ⟨x, hx, rfl⟩, ?_⟩
      show T (φ x) = _
      rw [hφe, hφr]
    · rintro ⟨_, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hL _).1 hu
      refine ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact (hφe _).trans (hφr x)
  have hleA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hleB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  constructor
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleA hleB hR).symm
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleB hleA hR).symm
end

