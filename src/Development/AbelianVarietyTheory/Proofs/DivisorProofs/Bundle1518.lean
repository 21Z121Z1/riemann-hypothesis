import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Norm

section Abstract

variable {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
  (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A)

theorem row_span {Z : Matrix (Fin r) (Fin n) A} {I : Set (Fin r)} {a : Fin r} (hz : ∀ i ∈ I, (Z * X) a i = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : (Z *ᵥ y) a = 0 := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.ker (LinearMap.proj a ∘ₗ Z.mulVecLin) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hz i hi
  exact this hy

theorem blk_mulVec (y : Fin n → A) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y =
      y + X.submatrix id e *ᵥ (P *ᵥ fun a => (K *ᵥ y) (e a)) + Y.submatrix id e *ᵥ (Q *ᵥ fun a => (L *ᵥ y) (e a)) := by
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rfl

theorem blk_span (hLX : L * X = 0) (hKX : K * X = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i _ => by rw [hLX]; rfl) hy
  rw [blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero]
  refine add_mem hy ?_
  rcases hI with hI | hI
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a, rfl⟩)
  · have h2 : (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hI a hi) hy
    rw [h2, mulVec_zero, mulVec_zero]
    exact zero_mem _

theorem blk_perp (hLX : L * X = 0) (hLY : L * Y = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : ∀ i ∈ I, (L *ᵥ y) i = 0) : ∀ i ∈ I,
    (L *ᵥ ((1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y)) i = 0 := by
  intro i hi
  have h1 : L * X.submatrix id e = 0 := by
    ext a b
    exact congrFun (congrFun hLX a) (e b)
  rw [blk_mulVec, mulVec_add, mulVec_add, mulVec_mulVec _ L (X.submatrix id e), h1, zero_mulVec, add_zero,
    Pi.add_apply, hy i hi, zero_add]
  rcases hI with hI | hI
  · have h2 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => hy _ (hI a)
    rw [h2, mulVec_zero, mulVec_zero, mulVec_zero]
    rfl
  · rw [mulVec_mulVec _ L]
    change ∑ a, (L * Y.submatrix id e) i a * _ = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (L * Y.submatrix id e) i a = 0 := by
      change (L * Y) i (e a) = 0
      rw [hLY, Matrix.one_apply_ne]
      rintro rfl
      exact hI a hi
    rw [this, zero_mul]

end Abstract

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

omit [NumberField E] in

theorem conj_mem_trivOn {A B B' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {m u : GAd σ J}
    (h1 : ∀ y ∈ A, (matHom _ σ J m).1 *ᵥ y ∈ A) (h2 : ∀ y ∈ A, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A)
    (h3 : ∀ y ∈ B, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ B') (hu : u ∈ trivOn σ J A B') : m * u * m⁻¹ ∈ trivOn σ J A B := by
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have e' : ∀ y, (matHom _ σ J m).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y = y := fun y => by
    simpa only [inv_inv] using e m⁻¹ y
  have i1 : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A := fun y => ⟨h1 y, fun h => e m y ▸ h2 _ h⟩
  have i2 : ∀ y, y ∈ A ↔ (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A := fun y => ⟨h2 y, fun h => e' y ▸ h1 _ h⟩
  have v : ∀ y, (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := fun y => by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec]
  refine ⟨fun y => by rw [v, ← i1, ← hu.1, ← i2], fun y hy => ?_⟩
  have := h1 _ (hu.2 _ (h3 y hy))
  rwa [mulVec_sub, e', ← v] at this

omit [NumberField E] in

theorem mem_trivOn_span {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {u : GAd σ J} {T : Set (Fin r)} {j : Fin r}
    (hj : j ∈ T) (hu : ∀ i ∈ T, u ∈ trivOn σ J A (colSpan F X {i})) : u ∈ trivOn σ J A (colSpan F X T) := by
  refine ⟨(hu j hj).1, fun y hy => ?_⟩
  have : colSpan F X T ≤ A.comap ((matHom _ σ J u).1.mulVecLin - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact (hu i hi).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact this hy

theorem blockEmb_normalises : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      (∀ g, ∀ u ∈ GlobalTheory.StdPar.unip σ J Xf S, ι g * u * (ι g)⁻¹ ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS _ _
  constructor
  · let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
    have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
        adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
    have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
    have hLY : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
      rw [hm, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have sp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colSpan F X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colSpan F X I := fun g I hI y hy => by
      rw [hι]
      exact blk_span (Y := adMat F Y) e _ _ hLX hKX hI hy
    have pp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colPerp σ J X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colPerp σ J X I := fun g I hI y hy => by
      rw [hι]
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      exact blk_perp (X := adMat F X) (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ hLX hLY hI hy
    have cp : ∀ p : Fin r → Prop, (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k ∧ p k} := fun p => by
      by_contra hc
      obtain ⟨h1, h2⟩ := not_or.1 hc
      obtain ⟨b, k, hk, hb, hp⟩ : ∃ b, e b ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k} := by simpa only [not_forall, not_not] using h2
      refine h1 fun a => ⟨k, hk, ?_, hp⟩
      have hb' : l + b.val ≤ k.val := hb
      have : ¬ k.val + 1 < l + d := fun h' => hS k (by omega) h' hk
      change l + a.val ≤ k.val
      omega
    have cp' : (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k} := by
      simpa only [and_true] using cp fun _ => True
    intro g u hu
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, conj_mem_trivOn (sp g cp') (map_inv ι g ▸ sp g⁻¹ cp')
      (map_inv ι g ▸ pp g⁻¹ cp') hu.2⟩
    have hu1 := Subgroup.mem_iInf.1 hu.1
    by_cases hj : j ∈ Set.range e
    · refine conj_mem_trivOn (B' := colSpan F X (Set.range e)) (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (fun y hy => map_inv ι g ▸ sp g⁻¹ (I := Set.range e) (Or.inl fun a => Set.mem_range_self a) y
          (Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj)) hy)) (mem_trivOn_span hj ?_)
      obtain ⟨b, rfl⟩ := hj
      rintro _ ⟨a, rfl⟩
      have key : ∀ a b : Fin d, ∀ k ∈ S, k < e a → k < e b := fun a b k hk hka => by
        have h1 : k.val < l + a.val := hka
        have h2 : ¬ l ≤ k.val := fun h' => hS k h' (by omega) hk
        change k.val < l + b.val
        omega
      have : {i | ∃ k ∈ S, i ≤ k ∧ k < e b} = {i | ∃ k ∈ S, i ≤ k ∧ k < e a} := Set.ext fun i =>
        ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩, fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩⟩
      rw [this]
      exact hu1 _
    · exact conj_mem_trivOn (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (map_inv ι g ▸ sp g⁻¹ (I := {j}) (Or.inr fun a (ha : e a = j) => hj (Exists.intro a ha))) (hu1 j)
  · have k1 : ∀ z, GlobalTheory.LFun.finTens F E (Φ.symm z) = (GlobalTheory.LFun.finAdEquiv F E).symm (GlobalTheory.CuspRep.pFin E z) := fun z => by
      have := congrArg (GlobalTheory.CuspRep.pFin E) (hΦ (Φ.symm z))
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]
      exact ((GlobalTheory.LFun.finAdEquiv F E).symm_apply_apply _).symm
    have k2 : ∀ y, ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := fun y => by
      have := congrArg Units.val (GlobalTheory.CuspRep.pFin_infGL (E := E) y)
      have e : ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) =
          ((GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E)).map (GlobalTheory.LFun.finAdEquiv F E).symm :=
        Matrix.ext fun a b => k1 _
      rw [e, show (GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E) = 1 from this]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have k3 : ∀ x, sigR (Af F) σ (GlobalTheory.LFun.finTens F E x) = GlobalTheory.LFun.finTens F E (sigR (AF F) σ x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => rfl
    intro y
    refine Units.ext ?_
    change (matHom _ σ J (ι (GlobalTheory.CuspRep.infGL E d y))).1.map (GlobalTheory.LFun.finTens F E) = 1
    have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).map (GlobalTheory.LFun.finTens F E) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hι, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), k2,
      ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ (sigR (Af F) σ) _ k3, ← map_inv, k2, o, o, Formalism.UG.cT_one, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GlobalTheory.BlockForms.Norm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_integral_of_local : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)
    (t : Fin q → ℝ) (m : ℕ) (ξ : κ → F) (j : κ),
    (∀ v : Pl F, evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) ∈ v.adicCompletionIntegers F) →
    IsIntegral ℤ ((m : F) * ξ j) := by
  first | exact @GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | exact GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem | (intros; apply GlobalTheory.ThKTorus.IntegralOfAdic.integral_of_evFin_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledNormDecayStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_scaled_norm_decay : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  first | exact @GlobalTheory.ThKTorus.MajCompare.weight_le_majorant | exact GlobalTheory.ThKTorus.MajCompare.weight_le_majorant | (intros; apply GlobalTheory.ThKTorus.MajCompare.weight_le_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | exact GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | (intros; apply GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDime
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.KilledFinCentre

theorem centre_orbit_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  intro E _ _ _ b q hq
  classical
  obtain ⟨T, hT, hZ⟩ := GlobalTheory.T.zalg_eq_adjoin_finite_capelli E b
  let p : Module.End ℂ (Sm E b) → Polynomial ℂ := fun t =>
    if h : ∃ τ u, t = cap τ u then q h.choose h.choose_spec.choose else 1
  have hp : ∀ t ∈ T, p t ≠ 0 := by
    intro t ht
    simp only [p]
    split_ifs with h
    · exact hq _ _
    · exact one_ne_zero
  have hkill : ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) →
      ∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0 := by
    intro ψ hψ t ht
    have h : ∃ τ u, t = cap τ u := hT t ht
    have key : ∀ τ u, t = cap τ u → Polynomial.aeval t (q τ u) ψ = 0 := by
      rintro τ u rfl; exact hψ τ u
    simp only [p, dif_pos h]
    exact key _ _ h.choose_spec.choose_spec
  have hc : ∀ s ∈ T, ∀ t ∈ T, Commute s t := fun s hs t ht =>
    GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hZ ▸ Algebra.subset_adjoin hs) (hZ ▸ Algebra.subset_adjoin ht)
  obtain ⟨X', hX', hX'e⟩ := GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector _ T p hc hp
  refine ⟨X', ∏ t ∈ T, (p t).natDegree, hX', fun ψ hψ => ?_⟩
  rw [hZ]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated _ T p hc hp ψ (hkill ψ hψ)
  exact ⟨h1, h2, hX'e ψ (hkill ψ hψ)⟩

end GlobalTheory.KilledFinCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLatticeGLConjLe
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem card_latticeGL_conj_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ A : ℕ,
    ∀ W : Set (GA E a), IsCompact W → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GL (Fin a) (Cinf E),
      {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.Finite ∧
      ({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℝ) ≤
        C * height y ^ (2 * A) := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩
    have hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton := fun s x _ z _ =>
      Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
    refine ⟨(hs _).finite, ?_⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2
  obtain ⟨m, hm⟩ := GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount E a
  refine ⟨m, fun W hW => ?_⟩
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact E a ha W hW
  obtain ⟨hInf, hFin, -, -⟩ := GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a
  set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he
  set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'
  have hW'c : IsCompact W' := (Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ =>
    hW.image (continuous_mul_right _)
  set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf
  have hKfc : IsCompact Kf := hW'c.image hFin
  have hv : Continuous fun g : GA E a =>
      ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val.comp hInf
  have ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a) := continuous_id
  have hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖ :=
    continuous_norm.comp (ht.comp hv)
  obtain ⟨B₀, hB₀⟩ := hW'c.exists_bound_of_continuousOn hcn.continuousOn
  set B : ℝ := max 0 B₀ with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B := fun w hw =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))
  obtain ⟨C₁, hC₁0, hC₁⟩ := hm Kf hKfc
  set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN
  set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) ^ 2 * B := by positivity
    linarith
  refine ⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩
  set T : ℝ := c * height y ^ 2 with hT
  have hh := one_le_height y
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)
  obtain ⟨hfin, hcard⟩ := hC₁ T hT1
  set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧
    Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS
  let f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a := fun p =>
    ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩
  have hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆
      f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀) := by
    rintro ⟨γ, hγ⟩ hγW
    obtain ⟨δ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
    change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW
    have hn : |n| ≤ n₀ := hn₀ δ n _ hγW
    have hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀ := abs_le.1 hn
    set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw
    have hcomm : Commute (e ^ n) (infGL E a y) :=
      (Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)
    have hwW : w ∈ W' := by
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩
      change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w
      simp only [mul_assoc]
      rw [← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]
      all_goals simp only [hw, mul_assoc]
    have hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹ := by rw [hw]; group
    refine ⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩
    · have e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) =
          y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹ := by
        rw [hδ, map_mul, map_mul, map_inv, pInf_infGL]
      rw [e1, Units.val_mul, Units.val_mul]
      have hw' := hBb w hwW
      have p1 := GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val
      have p2 := GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val
      have hy1 : ‖toL y.val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
      have hy2 : ‖toL (y⁻¹).val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL y.val)]
      have n1 := norm_nonneg (toL y.val)
      have n2 := norm_nonneg (toL (y⁻¹).val)
      have n3 := norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B) :=
        p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)
      have q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤
          a * ((a * (height y * B)) * height y) :=
        p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)
      refine q2.trans ?_
      rw [hT, hc]
      have : 0 ≤ height y ^ 2 := by positivity
      nlinarith
    · have e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) =
          Matrix.GeneralLinearGroup.map (pFin E) w := by
        rw [hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
      rw [e2]
      exact ⟨w, hwW, rfl⟩
  have hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite := (hfin.prod (Set.finite_Icc _ _)).image f
  refine ⟨hfin2.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub hfin2
  have k2 := Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))
  rw [Set.ncard_prod] at k2
  have k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤
      (S.ncard : ℝ) * N := by rw [hN]; exact_mod_cast k1.trans k2
  refine k3.trans ?_
  have hN0 : 0 ≤ N := by positivity
  calc (S.ncard : ℝ) * N ≤ C₁ * T ^ m * N := mul_le_mul_of_nonneg_right hcard hN0
    _ = C₁ * c ^ m * N * height y ^ (2 * m) := by rw [hT, mul_pow, ← pow_mul, mul_comm 2 m]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitaryStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  first | exact @GlobalTheory.ConjCartan.conj_cartan_arch | exact GlobalTheory.ConjCartan.conj_cartan_arch | (intros; apply GlobalTheory.ConjCartan.conj_cartan_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
section
noncomputable section

namespace GlobalTheory.ChartGraph

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def chartMatrixTopBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def chartBottomLeftBlock (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (mat (nmat X z) τ).submatrix (fun m => ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩)
    (Fin.castLE X.p0_le)

def graphCoord (X : Data E r) (z : V (nd X)) : X.Coord := fun τ => chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹

end GlobalTheory.ChartGraph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  first | exact @GlobalTheory.DerCont.continuous_foldr_lineDer | exact GlobalTheory.DerCont.continuous_foldr_lineDer | (intros; apply GlobalTheory.DerCont.continuous_foldr_lineDer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbeddingStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.PhiIndep.phiC_indep | exact GlobalTheory.PhiIndep.phiC_indep | (intros; apply GlobalTheory.PhiIndep.phiC_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindexStatement
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxChange_realised_comp_and_reindex : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' := by
  first | exact @GlobalTheory.TowU.RealComp.realised_comp_reix | exact GlobalTheory.TowU.RealComp.realised_comp_reix | (intros; apply GlobalTheory.TowU.RealComp.realised_comp_reix <;> assumption)
end

