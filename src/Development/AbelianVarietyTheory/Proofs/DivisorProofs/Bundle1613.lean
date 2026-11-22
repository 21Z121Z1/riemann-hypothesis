import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxTransfersHaarFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatDarbouxTransfer

theorem finrank_AE (D : D7) : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) ∧
    Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin, D.sp.cm.deg2]⟩

theorem finrank_pair (K : Type) [Field K] (κ : Type) [Fintype κ] :
    Module.finrank K ((κ → K) × (κ → K)) = 2 * Fintype.card κ := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  ring

theorem finrank_mat (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (m n : ℕ) :
    Module.finrank K (Matrix (Fin m) (Fin n) L) = m * n * Module.finrank K L := by
  show Module.finrank K (Fin m → Fin n → L) = _
  simp [Module.finrank_pi_fintype, mul_assoc]

theorem card_eq (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) :
    Fintype.card κ = T.rank * S.rank := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have h := e.finrank_eq
  have ha : Module.finrank (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) = T.rank * S.rank * 2 := by
    show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AE D) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  have : T.rank * S.rank * 2 = 2 * Fintype.card κ := ha.symm.trans (h.trans hb)
  omega

set_option maxHeartbeats 1000000 in
theorem onto (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, e.symm p ∈ ratL T S := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have hκ := card_eq D S T κ e
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
    LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
  let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) := J1.prodMap J1
  let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars D.host.F).comp I
  haveI : Nontrivial (AE D) := Module.nontrivial_of_finrank_pos (R := AF D.host.F) (by rw [hAE]; norm_num)
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    refine (finrank_mat D.host.F D.host.E T.rank S.rank).trans ((finrank_pair D.host.F κ).trans ?_).symm
    rw [hκ, D.sp.cm.deg2]
    ring
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM D.host.F x) = J (y, z) := hx
  show incM D.host.F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

end GlobalTheory.RatDarbouxTransfer

namespace GlobalTheory.RatDarbouxTransfer

open scoped Pointwise

set_option maxHeartbeats 1000000 in

theorem haar_fundDomain_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro D ψ _ S T JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  haveI hMT : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  let ce : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃L[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : Formalism.IndefR.Datum.WO S T ≃ₜ+ (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : Formalism.IndefR.Datum.WO S T ≃ᵐ (κ → AF D.host.F) × (κ → AF D.host.F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratL T S, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, co.e.symm p ∈ ratL T S :=
    onto D S T κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : Formalism.IndefR.Datum.WO S T) + x) = co.e g + co.e x
      rw [map_add]
    · intro p q hpq
      let g : ratL T S := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratL T S := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratL T S => co.e (t : Formalism.IndefR.Datum.WO S T)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) (k : ratL T S),
          (k : Formalism.IndefR.Datum.WO S T) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF D.host.F) × (κ → AF D.host.F)) + co.e w = co.e ((k : Formalism.IndefR.Datum.WO S T) + w)
        rw [map_add, hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotent
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem col_coeff {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {g : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) (j : Fin r) :
    ∃ c : Fin r → AF F ⊗[F] E, (∀ i, j ≤ i → c i = 0) ∧
      (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j + adMat F X *ᵥ c := by
  have h := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 h
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, -, hik, hkj⟩ := hl (Finsupp.mem_support_iff.2 hne)
    exact absurd (hik.trans_lt hkj) (not_lt.2 hi)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e
    beta_reduce at e
    have e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i := by
      rw [Matrix.mulVec_eq_sum]; simp only [op_smul_eq_smul]
    rw [e2, e, add_sub_cancel]

omit [NumberField E] in

theorem par_of_unip {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {s : ℕ} (hs : s ≤ r) {d : Fin s → ℕ}
    (hd : Monotone d) {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) :
    ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B := by
  choose c hc hce using col_coeff hg
  refine ⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩
  · have hji : j < i := not_le.1 fun h => absurd hlt (not_lt.2 (hd h))
    have hle : Fin.castLE hs j ≤ Fin.castLE hs i := by
      rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hji.le
    simp [Matrix.one_apply_ne hji.ne', hc _ _ hle]
  · ext k j
    have h1 := congrFun (hce (Fin.castLE hs j)) k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1
    rw [Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢
    rw [h1]
    congr 1
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)
    have : s ≤ i.val := by
      by_contra hlt
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    rw [hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]

end GlobalTheory.RatLevi

theorem GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT
  obtain ⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1 := ⟨_, rfl⟩
  have hs : s ≤ r := hsdef ▸ Finset.sup_le fun k _ => k.2
  have hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := fun i => by
    rw [hsdef, Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card := ⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩
  have hdm : Monotone d := fun i j hij => by
    rw [hddef, hddef]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩
    rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hij
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef
  have hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d :=
    ⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩
  obtain ⟨u, huF, m, hmF, hpm, hr⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 _ hp
  refine ⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩
  rw [← inv_inv γ, hpm, mul_inv_rev]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealTraceArchimedeanEmbeddingsNondegenerate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfTraceNondeg

variable {K : Type} [Field K] [NumberField K]

theorem norm_algebraMap_apply (x : K) (v : InfinitePlace K) :
    ‖(algebraMap K (InfiniteAdeleRing K) x) v‖ = v x := by
  exact InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm x)

theorem norm_eq_of_cont (χ : InfiniteAdeleRing K →+* ℂ) (hχ : Continuous χ) (φ : K →+* ℂ)
    (h : ∀ x, χ (algebraMap K _ x) = φ x) (a : InfiniteAdeleRing K) :
    ‖χ a‖ = ‖a (InfinitePlace.mk φ)‖ := by
  have hc1 : Continuous fun a => ‖χ a‖ := hχ.norm
  have hc2 : Continuous fun a : InfiniteAdeleRing K => ‖a (InfinitePlace.mk φ)‖ :=
    (continuous_apply (InfinitePlace.mk φ)).norm
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap K).equalizer hc1 hc2 (funext fun x => ?_)) a
  simp only [Function.comp, h, norm_algebraMap_apply, InfinitePlace.apply]

end GlobalTheory.InfTraceNondeg

example (D : D7) (ρ : D.what₂.Tau) : Formalism.MainNotions.StandardLattice.embOf D ρ = tauE D ρ := rfl

namespace GlobalTheory.InfTraceNondeg

set_option synthInstance.maxHeartbeats 400000 in

theorem realTrace_nondeg : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  intro D θ hθ a ha
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 w
  let χ : D.what₂.Tau → (Ainf D.host.F →+* ℂ) := fun σ =>
    (θ σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hχapp : ∀ σ c, χ σ c = θ σ (c ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ _ => rfl
  have hχalg : ∀ σ (x : D.host.F), χ σ (algebraMap D.host.F (Ainf D.host.F) x) =
      ((tauE D σ).comp (algebraMap D.host.F D.host.E)) x := by
    intro σ x
    rw [hχapp, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', (hθ σ).1]
    rfl
  have hnorm : ∀ σ c, ‖χ σ c‖ = ‖c (InfinitePlace.mk ((tauE D σ).comp (algebraMap D.host.F D.host.E)))‖ :=
    fun σ c => norm_eq_of_cont (χ σ) (hθ σ).2 _ (hχalg σ) c
  have hmul : ∀ x y : Ainf D.host.F, ∀ u, (x * y) u = x u * y u := fun _ _ _ => rfl
  set e : Ainf D.host.F := Pi.single v 1 with he
  set b : Ainf D.host.F := Pi.single v (a v)⁻¹ with hb
  have hab : a * b = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu
      simp [he, hb, hv]
    · simp [he, hb, Pi.single_apply, hu]
  have hee : e * e = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu; simp [he]
    · simp [he, Pi.single_apply, hu]
  have hidem : ∀ σ, χ σ e = 0 ∨ χ σ e = 1 := by
    intro σ
    have h1 : χ σ e * χ σ e = χ σ e := by rw [← map_mul, hee]
    have h2 : χ σ e * (χ σ e - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hplace : InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E)) = v := by
    rw [← InfinitePlace.comap_mk]
    change (InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ)).comap _ = v
    have hρ' : InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ) = w := hρ
    have hw' : w.comap (algebraMap D.host.F D.host.E) = v := hw
    rw [hρ', hw']
  have hρ1 : χ ρ e = 1 := by
    rcases hidem ρ with h | h
    · exfalso
      have := hnorm ρ e
      rw [h, hplace, he, Pi.single_eq_same, norm_zero, norm_one] at this
      exact zero_ne_one this
    · exact h
  refine ⟨b, ?_⟩
  rw [hab, Complex.re_sum]
  have hterm : ∀ σ, 0 ≤ (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re := by
    intro σ
    rw [← hχapp]
    rcases hidem σ with h | h <;> simp [h]
  have hge : (θ ρ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re ≤ ∑ σ, (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re :=
    Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ ρ)
  rw [← hχapp, hρ1, Complex.one_re] at hge
  linarith

end GlobalTheory.InfTraceNondeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTargetF

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dblG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin (n + n)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl J)

theorem isHermND_dblG {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) :
    IsHermND σ (dblG J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;>
      simp [dbl, h.1 i j]
  · rw [dblG, Matrix.det_reindex_self, dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp [h.2]

theorem reindex_dbl_incM {n : ℕ} {J JA : Matrix (Fin n) (Fin n) E} (hA : JA = Jᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl (incM F JA)) = incM F (dblG J)ᵀ := by
  subst hA
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [dblG, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.map_apply] <;> simp [dbl]

abbrev coDbl {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) :
    Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) (κ ⊕ κ) :=
  reindexRows finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA)

theorem coDbl_rat {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ ⊕ κ → F,
      (coDbl hA co).e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro x
  obtain ⟨y₁, z₁, h₁⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inl) id)
  obtain ⟨y₂, z₂, h₂⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inr) id)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e₁ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inl id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
  have e₂ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inr id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
  rw [coDbl, reindexRows_e, dblRows_e, e₁, e₂, h₁, h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;> simp

theorem isHeckeCharF_one : Formalism.IndefR.DatumF.IsHeckeCharF (1 : (AF F ⊗[F] E)ˣ →* Circle) :=
  ⟨continuous_const, fun _ => rfl⟩

theorem resEtaF_one_dbl (h2 : Module.finrank F E = 2) {χ : (AF F ⊗[F] E)ˣ →* Circle} {n : ℕ}
    (hr : Formalism.IndefR.DatumF.ResEtaF χ n) : Formalism.IndefR.DatumF.ResEtaF (1 : (AF F ⊗[F] E)ˣ →* Circle) (n + n) :=
  ⟨hr.1, fun η hη a => by
    have h4 := hη.2.2.1 (Formalism.IndefR.DatumF.idFF F E a)
    have h5 : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Formalism.IndefR.DatumF.idFF F E a) = a ^ 2 :=
      Units.ext (by
        change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) a.1) = _
        have : Nontrivial (AF F) :=
          (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
        rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = η a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def ugDbl {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ) :
    UG (cA σ) (dbl (incM F JA)) →* UG (cA σ) (incM F (dblG JT)ᵀ) :=
  ugReindex finSumFinEquiv (reindex_dbl_incM hA)

theorem ugDbl_coe {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ)
    (g : UG (cA σ) (dbl (incM F JA))) :
    (ugDbl hA g).1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv g.1.1 := rfl

end GlobalTheory.WeilSchrodinger.DblTargetF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeCentreStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeCentre' : RelativeCentre := by
  first | exact @GlobalTheory.LeviHC.relativeCentre | exact GlobalTheory.LeviHC.relativeCentre | (intros; apply GlobalTheory.LeviHC.relativeCentre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasureStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subMeanValue_flagChart_invariantMeasure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  first | exact @GlobalTheory.SubmeanChart.submean_chart | exact GlobalTheory.SubmeanChart.submean_chart | (intros; apply GlobalTheory.SubmeanChart.submean_chart <;> assumption)
end

