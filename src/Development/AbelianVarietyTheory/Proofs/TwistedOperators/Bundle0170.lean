import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain.VacVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

private theorem Jm_mul_Jm_eq_oneFormalDegree {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conjTranspose_Jm_eq_Jm {n : ℕ} (ε : Fin n → Bool) :
    Matrix.conjTranspose (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conj_cartan_involution_props {n : ℕ} (F J : Matrix (Fin n) (Fin n) ℂ) (hF : IsUnit F) (hJ : J * J = 1)
    (hJh : Matrix.conjTranspose J = J) :
    F⁻¹ * J * F * (F⁻¹ * J * F) = 1 ∧
      Matrix.conjTranspose (F⁻¹ * J * F) * (Matrix.conjTranspose F * J * F) * (F⁻¹ * J * F) =
        Matrix.conjTranspose F * J * F ∧
      Matrix.conjTranspose F * J * F * (F⁻¹ * J * F) = Matrix.conjTranspose F * F := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hdh : IsUnit (Matrix.conjTranspose F).det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
    exact Matrix.nonsing_inv_mul F hd
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hJh, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hdh, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]

open Matrix in
open scoped ComplexOrder in

theorem cart_isCartanInv {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  unfold IsCartanInv cart
  rw [← M.fr_gram τ]
  obtain ⟨h1, h2, h3⟩ := conj_cartan_involution_props _ _ (M.fr_unit τ) (Jm_mul_Jm_eq_oneFormalDegree (M.ε τ)) (conjTranspose_Jm_eq_Jm (M.ε τ))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hinj : Function.Injective (M.fr τ).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (M.fr_unit τ)
  simpa only [Matrix.mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

private theorem exists_isVacVec_of_isSelfDualC {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') : ∃ f, IsVacVec ψ θ M M' f := by
  obtain ⟨f, hne, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W (cart M) (cart M')
    (cart_isCartanInv M) (cart_isCartanInv M') L L' hL hL'
  have hone : (fun w => (1 : ℂ) * f w) = f := funext fun w => one_mul (f w)
  obtain ⟨hth, -, hvac⟩ := hf 1
  rw [hone] at hth hvac
  exact ⟨f, ⟨hth, hne, hvac⟩⟩

theorem exists_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) :
    ∃ f, IsVacVec ψ θ M M' f :=
  exists_isVacVec_of_isSelfDualC ψ θ M M' hψ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame W)

theorem exists_char_fam_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') :
    ∃ ψ θ f, IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ IsVacVec ψ θ M M' f := by
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨f, hf⟩ := exists_isVacVec ψ θ M M' hψ hθ
  exact ⟨ψ, θ, f, hψ, hθ, hf⟩

end GlobalTheory.Chain.VacVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchRest

theorem exists_rest_arch : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  intro F _ _ κ _
  classical
  let I : Set (FiniteAdeleRing (𝓞 F) F) := (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hIo : IsOpen I := GroundTheory.Global.isOpen_integralFiniteAdeles
  have hIc : IsClosed I :=
    AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo
  have hIk : IsCompact I := GroundTheory.Global.isCompact_integralFiniteAdeles F
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => I
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hIo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => hIc
  have hSk : IsCompact S := isCompact_univ_pi fun _ => hIk
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ S
    · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
    · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  refine ⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩
  · have h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply]
    exact one_ne_zero
  · intro x z hz
    have hz2 : ∀ i, (z i).2 = 0 := by
      let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
      have e := hz u (by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _)
      intro i
      have e' := congrFun e i
      have h1 : (u • z) i = u * z i := rfl
      rw [h1] at e'
      have h2 : (u * z i).2 = 1 * (z i).2 := rfl
      have := congrArg Prod.snd e'
      rw [h2, one_mul] at this
      exact this
    show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · have e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g := rfl
    rw [e]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ArchRest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericSeries_squarefreeLabels : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  first | exact @GlobalTheory.GLq.SqSeries.exists_series | exact GlobalTheory.GLq.SqSeries.exists_series | (intros; apply GlobalTheory.GLq.SqSeries.exists_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChain
section
open scoped Matrix

namespace GlobalTheory.Flag

theorem exists_sup_eq_finrank_sub {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {A B : Submodule K V} (hAB : A ≤ B) :
    ∃ C : Submodule K V, C ⊔ A = B ∧
      Module.finrank K C = Module.finrank K B - Module.finrank K A := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl A
  have hsup : q ⊓ B ⊔ A = B := by
    rw [inf_comm, inf_sup_assoc_of_le _ hAB, sup_comm, hq.sup_eq_top, inf_top_eq]
  refine ⟨q ⊓ B, hsup, ?_⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (q ⊓ B) A
  have h2 : q ⊓ B ⊓ A = ⊥ := by
    refine eq_bot_iff.2 (le_trans ?_ hq.inf_eq_bot.le)
    rw [inf_comm A q]; exact inf_le_inf_right _ inf_le_left
  rw [hsup, h2, finrank_bot] at h1
  omega

theorem exists_gl_adapted_chain : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)), Monotone Y → Y 0 = ⊥ → Y (Fin.last m) = ⊤ →
    ∃ (d : Fin m → ℕ) (h : ∑ j, d j = n) (g : GL (Fin n) K), ∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0 := by
  intro K _ n m Y hmono h0 htop
  let r : Fin (m + 1) → ℕ := fun j => Module.finrank K (Y j)
  have hC : ∀ j : Fin m, ∃ C : Submodule K (Fin n → K), C ⊔ Y j.castSucc = Y j.succ ∧
      Module.finrank K C = r j.succ - r j.castSucc :=
    fun j => exists_sup_eq_finrank_sub (hmono (Fin.castSucc_le_succ j))
  choose C hCsup hCrk using hC
  let d : Fin m → ℕ := fun j => r j.succ - r j.castSucc
  let R : ℕ → ℕ := fun k => r ⟨min k m, by omega⟩
  have hRmono : Monotone R := by
    intro a b hab
    exact Submodule.finrank_mono (hmono (Fin.mk_le_mk.2 (min_le_min_right m hab)))
  have hsum : ∑ j, d j = n := by
    have e1 : ∑ j, d j = ∑ k ∈ Finset.range m, (R (k + 1) - R k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      have a1 : (⟨min ((j : ℕ) + 1) m, by omega⟩ : Fin (m + 1)) = j.succ := Fin.ext (by simp)
      have a2 : (⟨min (j : ℕ) m, by omega⟩ : Fin (m + 1)) = j.castSucc := Fin.ext (by simp)
      simp only [d, R, a1, a2]
    rw [e1, Finset.sum_range_tsub hRmono]
    have a3 : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    have a4 : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    have hRm : R m = n := by
      show Module.finrank K (Y ⟨min m m, _⟩) = n
      rw [a3, htop, finrank_top, Module.finrank_fin_fun]
    have hR0 : R 0 = 0 := by
      show Module.finrank K (Y ⟨min 0 m, _⟩) = 0
      rw [a4, h0, finrank_bot]
    rw [hRm, hR0, Nat.sub_zero]
  let B : ∀ j : Fin m, Module.Basis (Fin (d j)) K (C j) := fun j => Module.finBasisOfFinrankEq K (C j) (hCrk j)
  let f : (Σ j : Fin m, Fin (d j)) → (Fin n → K) := fun p => (B p.1 p.2 : Fin n → K)
  have hspanC : ∀ j : Fin m, Submodule.span K (Set.range fun i => f ⟨j, i⟩) = C j := by
    intro j
    have : (Set.range fun i => f ⟨j, i⟩) = (C j).subtype '' Set.range (B j) :=
      Set.range_comp (C j).subtype (B j)
    rw [this, Submodule.span_image, (B j).span_eq, Submodule.map_subtype_top]
  have hspan : ∀ k (hk : k ≤ m), Y ⟨k, by omega⟩ = Submodule.span K (f '' {p | (p.1 : ℕ) < k}) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have hset : f '' {p | (p.1 : ℕ) < k + 1} =
          (Set.range fun i => f ⟨⟨k, hk⟩, i⟩) ∪ f '' {p | (p.1 : ℕ) < k} := by
        ext v
        constructor
        · rintro ⟨⟨a, i⟩, hp, rfl⟩
          simp only [Set.mem_setOf_eq] at hp
          by_cases ha : (a : ℕ) < k
          · exact Or.inr ⟨⟨a, i⟩, ha, rfl⟩
          · obtain rfl : a = ⟨k, hk⟩ := Fin.ext (by simp; omega)
            exact Or.inl ⟨i, rfl⟩
        · rintro (⟨i, rfl⟩ | ⟨p, hp, rfl⟩)
          · exact ⟨⟨⟨k, hk⟩, i⟩, by simp, rfl⟩
          · exact ⟨p, by simp only [Set.mem_setOf_eq] at hp ⊢; omega, rfl⟩
      have e1 : (⟨k + 1, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).succ := rfl
      have e2 : (⟨k, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).castSucc := rfl
      rw [hset, Submodule.span_union, hspanC, ← ih (by omega), e1, e2, hCsup]
  let b : Fin n → (Fin n → K) := fun i => f ((GlobalTheory.SmGL.stdBlocks d hsum).symm i)
  have hsub : ∀ j : Fin (m + 1), f '' {p | (p.1 : ℕ) < j} = b '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j} := by
    intro j
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum) p, by simpa [GlobalTheory.SmGL.blk] using hp, by simp [b]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum).symm i, hi, rfl⟩
  have htopb : ⊤ ≤ Submodule.span K (Set.range b) := by
    have h1 := hspan m le_rfl
    have h2 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    have h3 := hsub (Fin.last m)
    rw [Fin.val_last] at h3
    rw [h2, htop, h3] at h1
    rw [h1]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hli : LinearIndependent K b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, top_unique htopb, finrank_top]
    simp
  let Bas : Module.Basis (Fin n) K (Fin n → K) := Module.Basis.mk hli htopb
  have hBas : ⇑Bas = b := Module.Basis.coe_mk hli htopb
  let pf := Pi.basisFun K (Fin n)
  let g : GL (Fin n) K := ⟨pf.toMatrix Bas, Bas.toMatrix pf, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hg : ∀ y : Fin n → K, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = ⇑(Bas.repr y) := by
    intro y
    have := Module.Basis.toMatrix_mulVec_repr pf Bas y
    have hy : ⇑(pf.repr y) = y := funext fun i => by simp [pf]
    rw [hy] at this
    exact this
  refine ⟨d, hsum, g, fun j y => ?_⟩
  have hYj : Y j = Submodule.span K (Bas '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j}) := by
    rw [hBas, ← hsub, ← hspan j (by omega)]
  rw [hYj, Module.Basis.mem_span_image, hg]
  constructor
  · intro hs i hi
    by_contra hne
    have := hs (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro H i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_lt] at hlt
    exact hi (H i hlt)

end GlobalTheory.Flag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslatesStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  first | exact @GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | exact GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | (intros; apply GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacuStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  first | exact @GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | exact GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | (intros; apply GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.ProdSupport

theorem piTensor_mulSingle {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (a : α) (g : Γ a) (c : ℂ) (h : ∀ v, ρ a g v = c • v) (y : ⨂[ℂ] a, X a) :
    piTensor ρ (Pi.mulSingle a g) y = c • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (c • x a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp [h]
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [h1, MultilinearMap.map_update_smul, Function.update_eq_self]

theorem nontrivial_piTensor {α : Type} [Fintype α] (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  have h1 : ∀ a, ∃ (x : X a) (l : Module.Dual ℂ (X a)), l x = 1 := fun a => by
    obtain ⟨x, hx⟩ := exists_ne (0 : X a)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    exact ⟨x, l, hl⟩
  choose x l hl using h1
  refine ⟨PiTensorProduct.tprod ℂ x, 0, fun h0 => ?_⟩
  have := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
  simp [hl] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_scalar_one {d : ℕ} (hd : d = 1) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin d) z) = z := by
  ext; simp [GeneralLinearGroup.scalar, hd]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem eq_scalar_det {d : ℕ} (hd : d = 1) (g : GL (Fin d) k) :
    g = GeneralLinearGroup.scalar (Fin d) (GeneralLinearGroup.det g) := by
  subst hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.val_det_apply]

theorem hasCentralChar_multiProd {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b))
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar (σ a) ω) : HasCentralChar (multiProd e σ) ω := by
  intro z f
  have h1 : leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) =
      GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by_contra fun h => (ha b h).elim y
    obtain rfl : b' = b := by_contra fun h => (ha b' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  have h3 : deltaHalf k c (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun b _ => ?_
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z))⟩ x
  rw [leviProj_leviEmb, h3, piTensor_mulSingle σ a _ _ (hω z)] at h4
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (ω z : ℂ) • f.1.1 x
  rw [hc, ← h1]
  simpa using h4

theorem exists_inSupport_of_multiProd : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α]
    (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ),
    (∀ a, IsSmooth (ρ a)) → (∀ a, (ρ a).IsIrreducible) → InSupport (multiProd e ρ) χ →
      ∃ a, InSupport (ρ a) χ := by
  intro hG k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ ρ χ hs hi
  rintro ⟨r, d, e', a, ha, Y, _, _, τ, hτ, hsub, hact⟩
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e' hs
    (fun i => hasFiniteLength_of_isIrreducible (hi i)) hτ hsub
  have hsum : ∑ i, b.1 i a = 1 := by simpa [ha] using b.2.2 a
  obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => b.1 j a) (Finset.mem_univ i)
  have hi1 : b.1 i a = 1 := by simp only at hsplit; omega
  have hz : ∀ j, j ≠ i → IsEmpty (Fin (b.1 j a)) := fun j hj => by
    have h0 : ∑ j ∈ Finset.univ.erase i, b.1 j a = 0 := by simp only at hsplit; omega
    rw [Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    infer_instance
  obtain ⟨ω, -, hω⟩ := LocGL.exists_smooth_hasCentralChar (s i a).smooth (s i a).irr
  have hcen := hasCentralChar_multiProd (g a) (fun j => (s j a).ρ) i hz hω
  obtain rfl : χ = ω := by
    have := Model.nontrivial_of_isIrreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine MonoidHom.ext fun z => ?_
    have h1 := Model.scalar_of_isSubquotient hcol
      (piTensor_mulSingle (fun j => multiProd (g j) fun i => (s i j).ρ) a _ _ (hcen z)) y
    rw [hact, det_scalar_one ha] at h1
    exact Units.ext (smul_left_injective ℂ hy h1)
  obtain ⟨Z, _, _, υ, hυ, hυs⟩ := IrrSubquot.exists_irreducible_subquotient _ _
    (piTensor fun j => (s i j).ρ)
    (nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (s i j).irr)
  refine ⟨i, r, b.1 i, f i, a, hi1, Z, _, _, υ, hυ, hυs.trans (hrow i), fun h y => ?_⟩
  refine Model.scalar_of_isSubquotient hυs (piTensor_mulSingle (fun j => (s i j).ρ) a h _ fun v => ?_) y
  conv_lhs => rw [eq_scalar_det hi1 h]
  exact hω _ v

end GlobalTheory.ProdSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidueStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V), finE V g ∈ St β → ∀ e : AE D, e * e = e → ∃ x : (AE D)ˣ, IsDetAt e V g x ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E, Formalism.L2.NTheta.IsIdemAt e PP → ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ := by
  first | exact @GlobalTheory.StabDet.exists_detAt_int | exact GlobalTheory.StabDet.exists_detAt_int | (intros; apply GlobalTheory.StabDet.exists_detAt_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsLocalLevelAtPrimeOfLevelDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalLevelAtPrimeOfLevelDatum : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  first | exact @GlobalTheory.StepVec.exists_isLocLevel | exact GlobalTheory.StepVec.exists_isLocLevel | (intros; apply GlobalTheory.StepVec.exists_isLocLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnitsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  first | exact @GlobalTheory.ChrOff.unrOff_of_unrAt | exact GlobalTheory.ChrOff.unrOff_of_unrAt | (intros; apply GlobalTheory.ChrOff.unrOff_of_unrAt <;> assumption)
end

