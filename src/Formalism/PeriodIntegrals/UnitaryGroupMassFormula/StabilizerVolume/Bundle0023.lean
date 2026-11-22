import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.KapIntegral

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensAAOf
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def ResAA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ (L : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (H : ℕ → AddSubgroup (HermR (Fv F v) σ a)),
      (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) = latV b v ∧
      IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧
      IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧ Λ 0 ≤ L ∧
      (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
      (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
      (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
      (∀ y ∈ L, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0 →
        ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
          (∀ n, (Λ n).map D = H n) ∧ ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈
              H (n + 1)) ∧
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧ (Nat.card k : ℝ) = qV v ∧
        ((μv ((L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∩
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0})) /
            νv (H 0)).toReal =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
            (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2)

theorem densAA_of (hFL : FibLat) (hFF : FFCount) (hR : ResAA) : DensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  obtain ⟨C, hC⟩ := hFF M
  refine ⟨C, ?_⟩
  filter_upwards [hR F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b] with v hv
  intro μv hμv νv hνv fibV hfib
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  obtain ⟨L, Λ, H, hL, hLo, hLc, hΛL, hΛo, hΛc, hΛa, hHo, hHc, hHb, hyp, k, K, _, _, _, _, σ', J',
    T', hQ, h2, hJ', hJu, hT', hTu, hq, hcnt⟩ := hv μv hμv νv hνv
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  have e := hFL _ _ _ μv νv hμv.1 hνv.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (continuous_gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (fun _ => rfl) _ _ fibV hfib
    (hermOf (Fv F v) σ (gramE σ J X0) hT) Filter.univ_mem _
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc
    hHb hyp
  rw [hcnt, hL] at e
  rw [e]
  have hb := hC k K σ' hQ h2 J' hJ' hJu a (by omega) T' hT' hTu
  rw [← hq]
  have : ((((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) : ℝ) : ℂ) - 1) =
      (((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hb

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibTop
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def FreeOpen : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  IsOpen {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen {X : Fin a → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVol
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW

theorem volAA_of (hC : CondAA) : VolAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ ψ hψ d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1

  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  filter_upwards [hC F ψ hψ, ev_dual b σ hσσ J hJ.2 (a := a), ev_dualH b σ hσσ a]
    with v hv hL hH

  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : SecondCountableTopology (Fv F v) := by
    haveI : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨_, Set.countable_range (algebraMap F (Fv F v)),
        HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)⟩⟩
    exact UniformSpace.secondCountable_of_separable _
  constructor
  ·
    intro μv hμ
    have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))
        ((latSub b v a M : AddSubgroup _) : Set (Fin a → Fin M → Fv F v ⊗[F] E)) =
        (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
      ann_eq v (psiV F ψ v) (BR (Fv F v) σ J) (latV (M := M) (n := a) b v) hv
        (smul_latV b v σ J) hL
    exact vol_one_of_ann hμ
      (fun X T Y => by simp only [BR_add, psiV_add]) (latSub b v a M)
      (isCompact_latV b v a M) (isClopen_latV b v a M).isOpen hA
  ·
    intro νv hν
    have hA : ann (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T))
        (hermO b v σ a : Set (HermR (Fv F v) σ a)) = hermO b v σ a :=
      ann_eq v (psiV F ψ v) (pairHerm (Fv F v) σ a) _ hv (smul_hermO b v σ a) hH
    exact vol_one_of_ann hν
      (fun S T U => by simp only [pairHerm_add, psiV_add]) (hermO b v σ a)
      (isCompact_hermO b v σ a).1 (isCompact_hermO b v σ a).2 hA

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PullLocSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Matrix
open scoped TensorProduct

def CompG : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ g : HA (AF F) σ J, ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v

def FibInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (h : HA (Ainf F) σ J) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      ∫ X, Φinf (h • X) ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def FibInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (h : HA (Fv F v) σ J) (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
      ∫ X, Φv (h • X) ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))

def smulHomeo {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  continuous_toFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
  continuous_invFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)

theorem pullLoc_of (hC : CompG) (hI : FibInvInf) (hV : FibInvV) : PullLoc := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs
    hpure hprod
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hInf, hv, h1, h2, h3⟩ := hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  let eI := smulHomeo (Ainf F) σ (a := a) J hInf
  let eV := fun v => smulHomeo (Fv F v) σ (a := a) J (hv v)
  refine ⟨fun Y => Φinf (hInf • Y), fun Y => ∏ᶠ v, Φv v (hv v • projV v Y),
    fun v Y => Φv v (hv v • Y), hcΦ.comp eI.continuous, hcs.comp_homeomorph eI, ⟨?_, ?_, fun _ => rfl⟩,
    ?_, ?_, ?_⟩
  · intro v
    exact ⟨(hpure.1 v).1.comp_continuous (eV v).continuous, (hpure.1 v).2.comp_homeomorph (eV v)⟩
  · filter_upwards [hpure.2.1, h3 d b] with v hv1 hv2
    funext Y
    simp only [hv1, Set.indicator, Pi.one_apply]
    by_cases hY : Y ∈ latV b v
    · rw [if_pos ((hv2 Y).2 hY), if_pos hY]
    · rw [if_neg (fun h => hY ((hv2 Y).1 h)), if_neg hY]
  · intro X
    show Φ (g • X) = Φinf (hInf • projInf X) * ∏ᶠ v, Φv v (hv v • projV v (projFin X))
    rw [hprod (g • X), h1 X, hpure.2.2]
    congr 1
    refine finprod_congr fun v => ?_
    rw [h2 v X]
  · exact fun μinf hμinf νinf hνinf fibInf hfi =>
      hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi hInf Φinf
        hcΦ hcs
  · exact fun v μv hμv νv hνv fibV hfv =>
      hV F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμv νv hνv fibV hfv (hv v) (Φv v)
        (hpure.1 v)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Filter Finset PI.VolStabS.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hL hLfin hTail
  classical
  refine ⟨Measure.sum fun S : Finset ι => kap m L S, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_eq_zero]
    intro S
    refine measure_mono_null ?_ (ae_iff.1 (kap_ae hL S))
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro h
    apply hx
    refine Filter.eventually_cofinite.2 ((S.finite_toSet).subset ?_)
    intro i hi
    by_contra hiS
    exact hi ((h i).2 hiS)
  · intro i C hC hCm
    rw [Measure.sum_apply_eq_zero]
    intro S
    apply kap_eval_null hC.compl
    simp only [mu]
    split_ifs
    · exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hCm.le)
    · exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hCm.le)
  · intro f hfi hf
    obtain ⟨T0, hT0⟩ : ∃ T0 : Finset ι, ∀ i ∉ T0, f i = (L i).indicator 1 :=
      ⟨(Filter.eventually_cofinite.1 hf).toFinset, fun i hi => by simpa using hi⟩
    have hsub : ∀ (S : Finset ι) (x : (i : ι) → W i), (∀ i, i ∉ S → x i ∈ L i) →
        Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ T0) := by
      intro S x hx i hi
      by_contra hni
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hni
      apply hi
      show f i (x i) = 1
      rw [hT0 i hni.2]
      simp [hx i hni.1]
    have hA : ∀ S : Finset ι, (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => ∏ i ∈ S ∪ T0, f i (x i) := by
      intro S
      filter_upwards [kap_ae hL S] with x hx
      exact finprod_eq_prod_of_mulSupport_subset _ (hsub S x fun i hi => (hx i).2 hi)
    have hZ : ∀ S : Finset ι, ¬ S ⊆ T0 →
        (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S] 0 := by
      intro S hS
      obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.1 hS
      filter_upwards [kap_ae hL S] with x hx
      refine finprod_eq_zero (fun i => f i (x i)) j ?_
        ((S ∪ T0).finite_toSet.subset (hsub S x fun i hi => (hx i).2 hi))
      rw [hT0 j hjT]
      simp [(hx j).1 hjS]
    have hint : ∀ S : Finset ι, Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) (kap m L S) :=
      fun S => (kap_integral hLfin hTail Finset.subset_union_left f hfi).1.congr (hA S).symm
    have hI : ∀ S : Finset ι, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        if S ⊆ T0 then (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ) else 0 := by
      intro S
      split_ifs with h
      · rw [integral_congr_ae (hA S), Finset.union_eq_right.2 h]
        exact (kap_integral hLfin hTail h f hfi).2
      · rw [integral_congr_ae (hZ S h)]
        simp
    have hρint : Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i))
        (Measure.sum fun S => kap m L S) := by
      refine integrable_sum_measure hint (summable_of_ne_finset_zero (s := T0.powerset) ?_)
      intro S hS
      rw [Finset.mem_powerset] at hS
      have h0 : (fun x : (i : ι) → W i => ‖∏ᶠ i, f i (x i)‖) =ᵐ[kap m L S] fun _ => (0 : ℝ) :=
        (hZ S hS).mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
      rw [integral_congr_ae h0, integral_zero]
    have hsum : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
        (∑ S ∈ T0.powerset, (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ)) := by
      have h : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
          (∑ S ∈ T0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S) :=
        hasSum_sum_of_ne_finset_zero (fun S hS => by rw [hI S, if_neg (by simpa using hS)])
      convert h using 1
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hI S, if_pos (Finset.mem_powerset.1 hS)]
    have hval : ∫ x, ∏ᶠ i, f i (x i) ∂(Measure.sum fun S => kap m L S) =
        (∏ i ∈ T0, ∫ w, f i w ∂m i) * ((tl m L T0 : ℝ) : ℂ) := by
      rw [(hasSum_integral_measure hρint).unique hsum, ← Finset.sum_mul]
      congr 1
      rw [show (∏ i ∈ T0, ∫ w, f i w ∂m i) =
          ∏ i ∈ T0, ((∫ w in (L i)ᶜ, f i w ∂m i) + ∫ w in L i, f i w ∂m i) from
        Finset.prod_congr rfl fun i _ => by rw [add_comm, integral_add_compl (hL i) (hfi i)],
        Finset.prod_add]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mem_powerset] at hS
      rw [← Finset.prod_sdiff hS, mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, hi]
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, (Finset.mem_sdiff.1 hi).2]
    refine ⟨hρint, ?_⟩
    rw [hval]
    have h1 : HasProd (fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1)
        (∏ i ∈ T0, ∫ w, f i w ∂m i) := by
      convert hasProd_prod_of_ne_finset_one (s := T0)
        (f := fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1) (fun i hi => if_neg hi) using 1
      all_goals first | infer_instance | exact Finset.prod_congr rfl fun i hi => (if_pos hi).symm
    have h2 : HasProd (fun i => (((({i | i ∉ T0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        ((tl m L T0 : ℝ) : ℂ) :=
      (hasProd_ind hTail T0).map ((Complex.ofRealHom.toMonoidHom).comp NNReal.toRealHom.toMonoidHom)
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
    convert h1.mul h2 using 1
    funext i
    by_cases hi : i ∈ T0
    · simp [hi, Set.mulIndicator_apply]
    · have hind : ∫ w, (L i).indicator (1 : W i → ℂ) w ∂m i = (((m i) (L i)).toReal : ℂ) := by
        rw [show (1 : W i → ℂ) = fun _ => (1 : ℂ) from rfl, integral_indicator_const _ (hL i)]
        simp [Measure.real]
      rw [hT0 i hi, hind]
      simp only [hi, if_false, one_mul, Set.mulIndicator_apply, Set.mem_setOf_eq, not_false_eq_true,
        if_true, am, ENNReal.coe_toNNReal_eq_toReal]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
section
noncomputable section

namespace PI.VolStabS.TopoGram

open Matrix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by
  rw [hform_eq, hform_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Formalism.UG.cT, vecMul_transpose]
  congr 1
  funext i
  exact RingHom.map_mulVec σ G x i

end PI.VolStabS.TopoGram

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Matrix
open scoped TensorProduct

theorem gramPres_holds : GramPres := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g X
  have hg : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR (AF F) J *
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J := g.2
  funext x y
  change hR (AF F) σ J (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR (AF F) σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

end PI.VolStabS
end
end

