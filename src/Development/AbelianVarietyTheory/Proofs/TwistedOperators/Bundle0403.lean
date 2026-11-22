import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0388
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPart
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal : OntoModEx := by
  first | exact @GlobalTheory.OntoModPf.ontoModEx | exact GlobalTheory.OntoModPf.ontoModEx | (intros; apply GlobalTheory.OntoModPf.ontoModEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInverses
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.MatrixLeftInverseLift

theorem matrix_left_inverse_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  intro F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂
  choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)
  let Zm : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of Z
  have hZm : ∀ u, evFin F v u = 0 → u • Zm = 0 := by
    intro u hu; ext i j; simpa [Zm] using hZA i j u hu
  have hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N := by
    intro π N hπ
    ext i j
    have h := hπ i j
    by_cases hij : i = j
    · subst hij; simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]
    · simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]
  have hM₁ := hmap π₁ N₁ hZ₁
  have hM₂ := hmap π₂ N₂ hZ₂
  refine ⟨Zm + 1, ?_, hM₁, hM₂⟩
  have hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]; abel
  have hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0 := by
    intro u hu
    rw [hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]; simp
  have hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0 := by
    intro π N hM hN
    have : π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1 := by
      rw [map_sub, map_mul, map_one]
    change π.mapMatrix ((Zm + 1) * K - 1) = 0
    rw [this]; change (Zm + 1).map π * K.map π - 1 = 0
    rw [hM, hN, sub_self]
  have e₁ := hπ π₁ N₁ hM₁ h₁
  have e₂ := hπ π₂ N₂ hM₂ h₂
  rw [← sub_eq_zero]
  ext i j
  apply hinj
  · intro u hu
    have := congrArg (fun m => m i j) (hAt u hu)
    simpa using this
  · simpa using congrArg (fun m => m i j) e₁
  · simpa using congrArg (fun m => m i j) e₂

end GlobalTheory.MatrixLeftInverseLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpsTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.OpsRowsTuple

theorem offS_badPl_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (w : Pl D.host.E) :
    OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) w ↔ GlobalTheory.Hk3.Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_ops_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ t : T, ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H, (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) ∧ GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h ∧ (∀ (c : Pl D.host.E → List ℤ → ℂ) P, GlobalTheory.Hk3.Good R t P → ∀ cc, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, h P cc x = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t
  have hgp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg := hgp.2.1
  have hoff := offS_badPl_iff R t
  have h0 : ∀ P, Good R t P → Good R A.μ0 P := fun P hP => (hg t P hP).2.2
  have hβ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  cases hβ with
  | intro n hβ =>
  have lev := fun P (hP : Good R t P) => GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hg _ P (h0 P hP)).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => h0 P hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have H := GlobalTheory.Hk3.OpsRows.exists_ops (θ := R.θ) (M := R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) R.ν0 R.fd0 hC.models.inf hC.models.ν0.1.1 hC.models.ν0.2
    hS.2.1 R.HE _ hC.models.HE (goodPart_le _ _ _ _ _) (Good R t)
    (fun P d B => ⟨fun hB => by
        have hP : Good R t P := by
          obtain ⟨_, _, _, _, hO, -⟩ := hB
          exact (hoff P).1 hO
        exact ⟨hP, (((lev P hP).2.1 _ d B).1 hB).2⟩,
      fun hB => ((lev P hB.1).2.1 _ d B).2 ⟨(hoff P).2 hB.1, hB.2⟩⟩)
    (fun P hP => (lev P hP).1)
    (fun P hP c U hU => by
      obtain ⟨hU1, hU2⟩ := (mem_goodPart _ _ _ _ _ _).1 hU
      refine (mem_goodPart _ _ _ _ _ _).2 ⟨(lev P hP).2.2.2.2 _ _ _ c hC.models.inf U hU1, fun v => ?_⟩
      have hfix : ∀ k ∈ hyp (Yc D 0) P, ∀ g, U v (g * k) = U v g := fun k hk g => by
        rw [GlobalTheory.Hk3.OpsRows.mult_lev hU1 v k ((lev P hP).1 k hk).1 g, ((lev P hP).1 k hk).2, one_mul]
      rw [postOn_apply]
      conv_rhs => rw [← hU2 v]
      simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      exact (lev P hP).2.2.2.1 c _ _ hfix)
  cases H with
  | intro h H2 =>
  exact ⟨h, H2.1, H2.2.1, fun c => H2.2.2.2.1 _, fun c => H2.2.2.2.2 _⟩

end GlobalTheory.Hk3.OpsRowsTuple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLineStatement
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
theorem _root_.GlobalTheory.T.exists_real_lie_operator_theta_quotient_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  first | exact @GlobalTheory.RealLieOp.exists_realOp | exact GlobalTheory.RealLieOp.exists_realOp | (intros; apply GlobalTheory.RealLieOp.exists_realOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterTrivialBoundUnramifiedUnitaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_trivialBound_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KU σ n) → (∀ h ∈ Hecke ℂ (KU σ n), ∃ c : ℂ, heckeVec ρ (KU σ n) h x = c • x) → ∃ α, IsSatVecU ϖ q ρ x α ∧ GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  first | exact @GlobalTheory.Twist.satParam_exists_trivialBound | exact GlobalTheory.Twist.satParam_exists_trivialBound | (intros; apply GlobalTheory.Twist.satParam_exists_trivialBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTypeIwahoriMaximalCompactIdempotentFamilyStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typeIwahoriMaximalCompact_idempotentFamily : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ v : T.S, e v = T.idem μf v) ∧ (∀ v, conv (μf v) (e v) (e v) = e v) ∧ (∀ k ∈ U.frame.iwahori, ∀ g, e U.u (k * g) = e U.u g) ∧ SphRest T U e ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → HasTypeVec T σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ≠ 0 := by
  first | exact @GlobalTheory.TrIdem.exists_idemFam | exact GlobalTheory.TrIdem.exists_idemFam | (intros; apply GlobalTheory.TrIdem.exists_idemFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacUnip

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

def uni (Z : Matrix n n A) : Matrix (n ⊕ n) (n ⊕ n) A := Matrix.fromBlocks (1 + Z) (-Z) Z (1 - Z)

theorem uni_mul_uni_neg (Z : Matrix n n A) : uni Z * uni (-Z) = 1 := by
  rw [uni, uni, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> noncomm_ring

def uniGL (Z : Matrix n n A) : GL (n ⊕ n) A :=
  ⟨uni Z, uni (-Z), uni_mul_uni_neg Z, by simpa using uni_mul_uni_neg (-Z)⟩

theorem uni_unitary (c : A →ₐ[R] A) (J Z : Matrix n n A) (h : Zᵀ * J + J * Z.map c = 0) :
    (uni Z)ᵀ * dbl J * (uni Z).map c = dbl J := by
  have h1 : (1 + Z).map c = 1 + Z.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h2 : (1 - Z).map c = 1 - Z.map c := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : (-Z).map c = - Z.map c := by
    ext i j; simp
  have h4 : J * Z.map c = - (Zᵀ * J) := eq_neg_of_add_eq_zero_right h
  rw [uni, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, h1, h2, h3, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_neg]
  generalize Z.map c = Zc at *
  generalize Zᵀ = Zt at *
  congr 1
  · calc _ = J + (Zt * J + J * Zc) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = -J + (Zt * J + J * Zc) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem uni_mul_diagCols (Z : Matrix n n A) : uni Z * (diagCols n : Matrix (n ⊕ n) n A) = diagCols n := by
  rw [uni, diagCols, Matrix.fromBlocks_mul_fromRows]
  congr 1 <;> simp

theorem smul_uni_sub_one (u : R) (Z : Matrix n n A) (h : u • Z = 0) : u • (uni Z - 1) = 0 := by
  have h' : ∀ i j, u • Z i j = 0 := fun i j => congrFun (congrFun h i) j
  ext (i | i) (j | j) <;> simp [uni, Matrix.one_apply, h']

theorem uni_mulVec_inl (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_sub]
  abel

theorem uni_mulVec_inr (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inr, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub]
  abel

theorem blocks_uni_mul (Z : Matrix n n A) (g : Matrix (n ⊕ n) (n ⊕ n) A) :
    (uni Z * g).toBlocks₁₁ + (uni Z * g).toBlocks₁₂ + (uni Z * g).toBlocks₂₁ + (uni Z * g).toBlocks₂₂ =
      g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂ +
        (Z + Z) * (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, uni, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  noncomm_ring

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_invOf_two_mem {v : Pl F} (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h0 : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [h0, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [map_inv₀, h2]

theorem uni_mulVec_mem {d : ℕ} (W : Spc F E d) (v : Pl F) (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ GlobalTheory.DblVac.latD W v, uni Z *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [uni_mulVec_inl]; exact add_mem hz.1 (hZ _ (sub_mem hz.1 hz.2))
  · rw [uni_mulVec_inr]; exact add_mem hz.2 (hZ _ (sub_mem hz.1 hz.2))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {p g : GlobalTheory.DblVac.UD σ W}
    (hp : p ∈ GlobalTheory.DblVac.KD σ W v) (hg : g ∈ GlobalTheory.DblVac.KD σ W v) : p * g ∈ GlobalTheory.DblVac.KD σ W v := by
  have hm : ∀ a b : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * b) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD b :=
    fun _ _ => rfl
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : GlobalTheory.DblVac.matD (p * g) - 1 =
        (GlobalTheory.DblVac.matD p - 1) * GlobalTheory.DblVac.matD g + (GlobalTheory.DblVac.matD g - 1) := by
      rw [hm]; noncomm_ring
    rw [e, smul_add, ← Matrix.smul_mul, hp.1 u hu, hg.1 u hu, Matrix.zero_mul, add_zero]
  · rw [hm, ← Matrix.mulVec_mulVec]
    exact (hp.2 _ (hg.2 z hz).1).1
  · rw [mul_inv_rev, hm, ← Matrix.mulVec_mulVec]
    exact (hg.2 _ (hp.2 z hz).2).2

theorem exists_unip : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  intro F E _ _ _ _ _ σ d W v h2 Y hAt hL hY
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin d) (Fin d) (AE F E), Z = ⅟(2 : AF F) • Y := ⟨_, rfl⟩
  have hZZ : Z + Z = Y := by
    rw [← two_smul (AF F) Z, hZ, smul_smul, mul_invOf_self, one_smul]
  have hZc : Z.map (cA σ) = ⅟(2 : AF F) • Y.map (cA σ) := by
    rw [hZ]; ext i j; simp
  have hZu : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [hZc, hZ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]
  have hZL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hZ, Matrix.smul_mulVec]
    exact GlobalTheory.LatAlmostAll.smul_mem_latAt W v (evFin_invOf_two_mem h2) (hL z hz)
  have hZL' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-Z) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [Matrix.neg_mulVec]
    exact neg_mem (hZL z hz)
  let p : GlobalTheory.DblVac.UD σ W := ⟨uniGL Z, uni_unitary (cA σ) (incM F W.J) Z hZu⟩
  have hp : p ∈ GlobalTheory.DblVac.KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨uni_mulVec_mem W v Z hZL z hz, uni_mulVec_mem W v (-Z) hZL' z hz⟩⟩
    refine smul_uni_sub_one u Z ?_
    rw [hZ, smul_comm, hAt u hu, smul_zero]
  refine ⟨p, hp, ⟨1, ?_⟩, fun g hg => ⟨mul_mem_KD hp hg, ?_⟩⟩
  · exact (uni_mul_diagCols Z).trans (Matrix.mul_one _).symm
  · have e : GlobalTheory.DblVac.matD (p * g) = uni Z * GlobalTheory.DblVac.matD g := rfl
    rw [GlobalTheory.DblVac.diagonalBlockOfMatrix, GlobalTheory.DblVac.diagonalBlockOfMatrix, e, blocks_uni_mul, smul_add, hZZ, Matrix.mul_smul]

end GlobalTheory.DblVacUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_pureTensor_restrictedFamily : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  first | exact @GlobalTheory.PureTensorExists.existsUnique_isPure | exact GlobalTheory.PureTensorExists.existsUnique_isPure | (intros; apply GlobalTheory.PureTensorExists.existsUnique_isPure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlathFactorisationOfTensorProduct
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory

theorem flathFactorisation_of_tensorProduct (h1 : GlobalTheory.Published.FlathTensorProduct)
    (h2 : GlobalTheory.Published.UnitaryIrreducibleAdmissible) : GlobalTheory.Published.FlathFactorisation := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  obtain ⟨R, ξ, B, hf⟩ := h1 F E σ hc n J hJ H π hπ
  have hirr : ∀ v, (smRep (Flath.finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (Flath.finFactor R v)) := by
    intro v
    haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
    exact GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr
      (fun K hK hK' => h2 F E σ hc n J hJ v (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr K hK hK')
  refine ⟨R, ξ, B, hf, hirr, fun L hL => ?_⟩
  haveI := hL
  have hu : ∀ᶠ v in cofinite, ‖ξ (.inr v)‖ = 1 := Sum.inr_injective.tendsto_cofinite.eventually hf.unit
  filter_upwards [hu, hf.eventually_fixed L, GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hv hfix hθ
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have sm : ∀ y, y ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) →
      y ∈ GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := by
    intro y hy
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep (Flath.finFactor R v) g y = y}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk
    exact Subgroup.isOpen_mono hle hKo
  have hξ : ξ (.inr v) ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix k hk
  let x : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := ⟨ξ (.inr v), sm _ hξ⟩
  have hx : x ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hξ k hk)
  have hx0 : x ≠ 0 := fun e => by
    have : ξ (.inr v) = 0 := congrArg Subtype.val e
    rw [this, norm_zero] at hv
    exact zero_ne_one hv
  have hline := GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep (Flath.finFactor R v)) (hirr v).1 (hirr v).2 x hx hx0
  refine le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hξ)
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))) ∈
      fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy'
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableLineDerivativeStatement
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
theorem _root_.GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X), ∀ Φ ∈ algF ψ θ ε A B,
      ∀ L : ℝ →+ WO (sgn ε M) X, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
        (fun x => deriv (fun t : ℝ => heisO ψ (sgn ε M) X (L t) Φ x) 0) ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF | exact GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF | (intros; apply GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_pureTensors : ∀ D : D7, FockPure D := by
  first | exact @GlobalTheory.FockPureTensor.fockPure | exact GlobalTheory.FockPureTensor.fockPure | (intros; apply GlobalTheory.FockPureTensor.fockPure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → Integrable (fun y : Mx D W.rank r => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y)) F w * star (G w) ∂μV) μ := by
  first | exact @GlobalTheory.CoefInteg.integrable_coef | exact GlobalTheory.CoefInteg.integrable_coef | (intros; apply GlobalTheory.CoefInteg.integrable_coef <;> assumption)
end

