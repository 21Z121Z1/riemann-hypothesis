import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | exact GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | (intros; apply GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuousStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanOneParameterFamily_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  first | exact @GlobalTheory.ArchFamilyCont.continuous_family | exact GlobalTheory.ArchFamilyCont.continuous_family | (intros; apply GlobalTheory.ArchFamilyCont.continuous_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ArchLinePreimage

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem smul_eq_zero_of_finPart_eq_zero (t : AE D) (ht : finPart D t = 0) (a : AF D.host.F)
    (ha : a.1 = 0) : a • t = 0 := by
  let ι : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F →ₗ[D.host.F] AF D.host.F :=
    (LinearMap.inr D.host.F (InfiniteAdeleRing D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)).comp
      (LinearMap.mulLeft D.host.F a.2)
  let g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map ι LinearMap.id
  let fL : AE D →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    TensorProduct.map (sndA D.host.F).toLinearMap LinearMap.id
  have hfL : fL t = finPart D t := rfl
  have key : ∀ s : AF D.host.F ⊗[D.host.F] D.host.E, a • s = g (fL s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [smul_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul b x =>
      have hab : a * b = ι b.2 := by
        refine Prod.ext ?_ ?_
        · show a.1 * b.1 = 0
          rw [ha, zero_mul]
        · rfl
      have h1 : a • (b ⊗ₜ[D.host.F] x : AE D) = (a * b) ⊗ₜ[D.host.F] x := rfl
      rw [h1, hab]
      rfl
    | add s₁ s₂ h₁ h₂ =>
      rw [smul_add, h₁, h₂, LinearMap.map_add, LinearMap.map_add]
  rw [key, hfL, ht, LinearMap.map_zero]

theorem arch_symm_lineAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS.symm (lineAt θ τ z 1)) := by
  intro D θ hθ ε S X d e cS hcS τ z u hu
  have hx : (lineAt θ τ z 1).map (finPart D) = 0 :=
    funext fun i => funext fun j => congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.1 1) i) j
  set y := cS.symm (lineAt θ τ z 1) with hydef
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [← hydef, hcS] at hy
  set c : D.host.E := if ε then -1 else 1 with hc
  have hc0 : c ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  set N : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (c • S.gram).map ((finPart D).comp (inclR (AF D.host.F))) with hN
  have hNdet : IsUnit N.det := by
    have hd : N.det = ((finPart D).comp (inclR (AF D.host.F))) (c • S.gram).det :=
      (RingHom.map_det ((finPart D).comp (inclR (AF D.host.F))) _).symm
    rw [hd]
    refine IsUnit.map _ (Ne.isUnit ?_)
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) (gram_det_ne S)
  have hM : (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
      Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = 0 := by
    have h3 := congrArg (fun m => Matrix.map m (finPart D)) hy
    simp only [Matrix.map_mul] at h3
    rw [hx] at h3
    exact h3
  have hM0 : (y.map (finPart D))ᵀ.submatrix e id = 0 := by
    calc _ = HMul.hMul (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
          Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) N⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right N _ hNdet).symm
      _ = 0 := by rw [hM, Matrix.zero_mul]
  have hent : ∀ i j, finPart D (y i j) = 0 := by
    intro i j
    have h4 := congrFun (congrFun hM0 (e.symm j)) i
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, Equiv.apply_symm_apply,
      id, Matrix.zero_apply] at h4
    exact h4
  have hu1 : u.1 = 0 := by
    have h5 : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 h5
  funext i j
  exact smul_eq_zero_of_finPart_eq_zero (y i j) (hent i j) u hu1

end GlobalTheory.ArchLinePreimage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  first | exact @GlobalTheory.ColKer.kerA_col_mul_real | exact GlobalTheory.ColKer.kerA_col_mul_real | (intros; apply GlobalTheory.ColKer.kerA_col_mul_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainChiPairMovedVectorColumnCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_attChr_chi {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem rowEntries_c_rev (τ : D.what₂.Tau) (i : Fin D.R.m) :
    (rowEntries D sc.cGap τ).c i.rev = cen D sc.cGap τ (D.R.m - i) := by
  show (num D sc.cGap τ).cen ((i.rev : ℕ) + 1) = _
  rw [Fin.val_rev, show D.R.m - (i + 1) + 1 = D.R.m - i by omega]
  rfl

theorem half_ceil (n : ℕ) : (((n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) / 2 + if Odd n then 1 / 2 else 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
    push_cast; ring
  · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast; ring

theorem det_compAt_ptGrid {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) (hn : n < D.R.m + 1)
    (τ : D.what₂.Tau) :
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (ptGrid W g n))).det =
      Matrix.det (g.2 ⟨n, hn⟩ τ).1 := by
  have hX : DefNode D.R.m (.grid n D.R.m) := ⟨Nat.lt_succ_iff.1 hn, rfl⟩
  have hW := posOnb_of_defNode W μ0 hL hX
  have hB : IsUnit (W.onb (.grid n D.R.m) τ).det := by
    have h := congrArg Matrix.det (hW τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  rw [ptGrid_le W g hn, compAt_kappa_snd g ⟨n, hn⟩ hW τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_right_comm, Ring.mul_inverse_cancel _ hB, one_mul]
  exact Matrix.det_submatrix_equiv_self (finCongr (rank_gridM G (Nat.lt_succ_iff.1 hn))) _

theorem om_ptGrid_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t i d hd
  have hp : DefPair D.R.m (.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi (i : ℕ) D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have hf : IsThetaFunO W.ψ _ _ (movedVec t S d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ _ _) W.θ τ
      (cplxO (G.cartS W.cart (.chi (i : ℕ) D.R.m) τ) (G.onT W.cart (.chi (i : ℕ) D.R.m) τ)) (movedVec t S d) :=
    GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ h1 h2 _
      (GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2) _ (S.N.u _).2
  have hrS : (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC ((i : ℕ) + 1) := rank_gridM G (by omega)
  have hrT : (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC (i : ℕ) := rank_gridM G (by omega)
  have key := GlobalTheory.FockReal.om_fockIn hL W W.onb hp (fun X hX τ => GlobalTheory.FockReal.onb_def hL W hX τ)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => hasInfExp_attChr_chi hL i.2 _ τ) (fun τ => hasInfExp_attChr_chi hL i.2 _ τ)
    (fun τ => (rowEntries D sc.cGap τ).c i.rev - (((rowSizes D).nC i.succ + 1) / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).c i.rev + (((rowSizes D).nC i.castSucc + 1) / 2 : ℕ))
    (fun τ => ?_) (fun τ => ?_) _ hf.1 hf.2 (ptGrid W g i) (ptGrid_mem W g i) (ptGrid W g (i + 1))
    (ptGrid_mem W g (i + 1)) 1
  · have e1 : fockIn W W.onb (.chi (i : ℕ) D.R.m) (movedVec t S d) 1 = movedVec t S d :=
      GlobalTheory.FiniteFock.pureTensorO_one _ _ _ _ _ _ _ _ _
    rw [show GlobalTheory.FockReal.realSubst W W.onb (.chi (i : ℕ) D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)) 1 = 1 from
      map_one _, e1] at key
    rw [key]
    congr 1
    simp only [GlobalTheory.FockReal.realChar, GridData.toPair, mt_negGA]
    simp only [det_compAt_ptGrid hL W g (i : ℕ) (by omega), det_compAt_ptGrid hL W g ((i : ℕ) + 1) (by omega)]
    simp only [colScal, detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm]
    rfl
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_succ, rank_gridM G (show (i : ℕ) + 1 ≤ D.R.m by omega),
      Int.cast_sub, Int.cast_natCast, half_ceil]
    ring
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_castSucc, hrT, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      half_ceil]
    ring

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopRowRealPointInOrthonormalBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

theorem mul_adaptedFrame_of_blocks {N r c N' : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (F : Matrix (Fin N) (Fin r) ℂ)
    (O Mmm : Matrix (Fin r) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (y : Matrix (Fin c) (Fin c) ℂ)
    (hr : r = c) (hc : c + 1 = N') (hN : N = N') (hO : IsUnit O.det)
    (h1 : A * F = F * Mmm) (h2 : Mmm = O * y.submatrix (Fin.cast hr) (Fin.cast hr) * O⁻¹) (h3 : A * Zc = Zc) :
    A * Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) =
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) *
      (Matrix.reindex (finSumFinEquiv.trans (finCongr hc)) (finSumFinEquiv.trans (finCongr hc))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast hN) (Fin.cast hN) := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have hK : (Matrix.reindex (e.trans (finCongr rfl)) (e.trans (finCongr rfl))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast rfl) (Fin.cast rfl) =
      (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext a k
    simp [Matrix.reindex_apply]
  rw [hT, hK, Matrix.submatrix_mul_equiv]
  have hL : A * (Matrix.fromCols (F * O) Zc).submatrix id e.symm = (A * Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    rfl
  rw [hL, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, h3]
  congr 2
  · rw [← Matrix.mul_assoc, h1, h2]
    simp only [Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.mul_zero, add_zero, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hO, Matrix.mul_one]
    congr 2
  · simp

theorem ptTop_inOnb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  intro D T L sc G μ0 hL W g n hn τ
  by_cases h : (n : ℕ) < D.R.m
  · have hP : PosOnb W (.top (⟨n, h⟩ : Fin D.R.m)) := posOnb_of_defNode W μ0 hL (X := .top (⟨n, h⟩ : Fin D.R.m)) h.le
    have hd : IsUnit (W.onb (.top (⟨n, h⟩ : Fin D.R.m)) τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
    have e1 := compAt_kappa_fst g ⟨n, h⟩ hP τ
    have e2 : ∀ k : Fin D.R.m, (rowComp (rowSizes D) g (Fin.castSucc k) τ).1 = (g.1 k τ).1 := fun k => by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrArg (fun x => (x τ).1) (Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j))
        (embed (rowSizes D).nC_succ (g.2 (Fin.last _))) g.1 k)
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, n = Fin.castSucc k := ⟨⟨n, h⟩, Fin.ext rfl⟩
    rw [ptTop_lt W g h]
    erw [e1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    erw [e2 k]
    rfl
  · have hm : (n : ℕ) = D.R.m := by have := n.2; omega
    obtain rfl : n = Fin.last D.R.m := Fin.ext hm
    have hF := hn rfl
    have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
    have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
    have hdT : IsUnit (topFrame W τ).det := by
      rw [← hF τ]; exact Matrix.isUnit_det_of_left_inverse (hPt τ)
    have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
    have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
          compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
    have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
        G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
    have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
        W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
          (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
      compAt_kappa_snd g (Fin.last D.R.m) hPg τ
    have hA := mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
      ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
      (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3
    have key : (topFrame W τ)⁻¹ * compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ =
        (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
          (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
      have hA' : compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
          (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
            (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := hA
      rw [Matrix.mul_assoc, hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdT, Matrix.one_mul]
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]; exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast, hF τ]
    exact key

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivative
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KHeisComm

variable {F : Type} [Field F] [NumberField F]

theorem archimedean_isomorphism_split_trivial {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.ArchIsom.r0 F κ (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = 1 := by
  change GlobalTheory.ArchIsom.g0 F κ 0 = 1
  simp [GlobalTheory.ArchIsom.g0, Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts (F := F) κ)]

theorem tens_split {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (GlobalTheory.ArchIsom.r0 F κ) (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = φ z := by
  have hz : (fun i => evI F (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0) i)) = z :=
    funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv κ _ i
  simp only [tens, hz, archimedean_isomorphism_split_trivial, mul_one]

open scoped Classical in

theorem proj_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end GlobalTheory.KHeisComm

open GlobalTheory.KHeisComm in
open scoped Classical in

theorem GlobalTheory.KHeisComm.actsD_heisLine_mat_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k _ u hu f f₁ fk h hD hA hA₁
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hDD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.HeisDeriv.exists_heisLine_deriv M B.ψ hψ (mat k * u)
  have hg0 := GlobalTheory.ArchIsom.standard_vector_mem_schwartz_bruhat (F := F) (Fin n × Fin d)

  have hf₁ : (D u f : SInf F (Fin n × Fin d)) = f₁ := by
    refine SchwartzMap.ext fun z => ?_
    set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
    have a1 : HasDerivAt (fun t => M.heisLine B.ψ u t (tens (evI F) (⇑f) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x)
        (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d)) x) 0 :=
      (hDD u hu f).1 _ hg0 _ (proj_mem_adm x)
    have a2 := hD _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f) x
    have e := a1.unique a2
    rw [← GlobalTheory.ArchIsom.tensor_at_standard_point, tens_split, tens_split] at e
    exact e
  suffices e : h = D₁ fk by rw [e]; exact hD₁ fk
  refine SchwartzMap.ext fun z => ?_
  set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
  have hl := hS.adm (k, 1) _ (proj_mem_adm x)
  have b1 := (hDD u hu f).1 _ hg0 _ hl
  have hmem : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) :=
    fun g => (GlobalTheory.ArchIsom.restriction_at_standard_point _ g).2
  have hfun : (fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (M.co.rho B.ψ (realAd F t • u) (pureA F (⇑f) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))))) =
      fun t => M.heisLine B.ψ (mat k * u) t (tens (evI F) (⇑fk) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x := by
    funext t
    rw [LinearMap.comp_apply, LinearMap.proj_apply, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hS.impl (k, 1) _ _ (hmem f),
      hA _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)]
    have hw : actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [hw]
    rfl
  have hval : ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))) = h z := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, hf₁, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hA₁ _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f₁),
      tens_split]
  rw [hfun, hval] at b1
  have b2 := hD₁ fk _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ fk) x
  rw [tens_split] at b2
  exact b1.unique b2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_field_type_vanishing : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishing := by
  first | exact @GlobalTheory.NonFieldType.nonFieldTypeVanishing | exact GlobalTheory.NonFieldType.nonFieldTypeVanishing | (intros; apply GlobalTheory.NonFieldType.nonFieldTypeVanishing <;> assumption)
end

