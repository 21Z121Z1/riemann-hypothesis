import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardMatrixStepIndicesLeExpStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_matrixStep_indices_le_exp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  first | exact @GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp | exact GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp | (intros; apply GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_near_neg_one_at_real_place : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  first | exact @GlobalTheory.NormSign.exists_norm_sign | exact GlobalTheory.NormSign.exists_norm_sign | (intros; apply GlobalTheory.NormSign.exists_norm_sign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToLStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  first | exact @GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | exact GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | (intros; apply GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweSpanFamiliesOfPlacesStatement
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeSpan_families_of_places : ∀ (ι : Type) [Fintype ι], HoweSpan ι := by
  first | exact @GlobalTheory.KJInf.howeSpan_all | exact GlobalTheory.KJInf.howeSpan_all | (intros; apply GlobalTheory.KJInf.howeSpan_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfIdeleNegOneNotMemClosurePrincipalIdentityCompStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infIdele_neg_one_not_mem_closure_principal_identityComponent : ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E), w.IsReal → ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) ∉ ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  first | exact @GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem | exact GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem | (intros; apply GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigenStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  first | exact @GlobalTheory.LowerHeckeEig.coeff_isEigen | exact GlobalTheory.LowerHeckeEig.coeff_isEigen | (intros; apply GlobalTheory.LowerHeckeEig.coeff_isEigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdealStatement
section
open MeasureTheory Matrix Formalism.IndefR.Datum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (a b r : ℕ), r ≤ a → r ≤ b → (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, ValuativeRel.valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation k (x i j) < 1}).toReal = (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | ∀ i j, ValuativeRel.valuation k (x i j) ≤ 1}).toReal * ((∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹)) * ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (r * (b - r)))⁻¹) := by
  first | exact @GlobalTheory.RectBlockVolume.vol_topBlock_KO | exact GlobalTheory.RectBlockVolume.vol_topBlock_KO | (intros; apply GlobalTheory.RectBlockVolume.vol_topBlock_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.MovedDatumS

theorem omPhi_locSmall_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 1 < N.R.m → ∀ (P : rowSG Pr sel mu) (h : AutY X N.R i) (h' : AutY X N.R (i + 1)), h ∈ stabL X.E _ (lamYat (Pr := Pr) i P.1) → h' ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1) → LocSmall (Formalism.L2.Col.qOf P.1) (lamYat (Pr := Pr) (R := N.R) i P.1) (lamYat (Pr := Pr) (R := N.R) (i + 1) P.1) (omPhi Ch sel mu cst i P h h') 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi P h h' hh hh'
  have hP : P.1 ∈ Pr.vGs :=
    (GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H).1 P.1 P.2
  have hs : cst.sharp = true := H.2.2.2.2.2.1
  unfold omPhi muAt
  unfold lamYat LocE.lamY at hh hh' ⊢
  refine GlobalTheory.ColNorms.MovedDatum.locSmall_om _ _ _ hh hh' ?_
  unfold PhiAt
  rw [hs]
  simp only [if_pos hP, if_true]
  have hq0 : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hN : ∀ j, N.R.N j = N.R.k + j * N.R.t + j := fun j => by unfold Ranks.N; ring
  have h2 := N.R.two_le_m
  refine GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small X.E X.K P.1 _ _ _ _ _ _ _ (i + 1) _ _ _ _ hq0 (Ideal.absNorm_mem _) ?_ ?_ ?_ ?_ ?_
  · rw [hN, Nat.add_sub_cancel]; unfold Formalism.L2.Col.cOf Ranks.r; omega
  · rw [hN, hN, add_mul]; unfold Formalism.L2.Col.cOf; omega
  · rw [hN]; omega
  · rw [hN]; omega
  · unfold Ranks.r; omega

end GlobalTheory.Core.Ht2.MovedDatumS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  first | exact @GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | exact GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | (intros; apply GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetMtOfAmbTie
section
open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem posAt_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : (H.map v.embedding).PosDef) : PosAt H v := by
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · simp only [hAt, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := h.1.apply i j
    simp only [Matrix.map_apply] at this
    rw [← this, star_star]
    ring
  · rw [hAt_eq_dot]
    have hx' : (fun i => v.embedding (x i)) ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := congrFun h0 i
      simpa using this
    exact (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hx')).1

theorem hAt_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

end GlobalTheory.Core.AmbTieStep

theorem GlobalTheory.Core.target_Mt_of_ambTie : ∀ (D : D7) (Gp : Type) [Group Gp] [Fintype Gp] (Pl0 Tu : Type) (m : ℕ) (A : FamIn D.what₂.LL Gp Pl0 Tu m) (Am : AmbForm D (RowSide.sharp D)) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : Tu → D.what₂.Tup) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb (tup t)) (J : AmbIds D A (RowSide.sharp D) Am P ψ tup), AmbTie D A (RowSide.sharp D) Am P ψ tup jA J → ∀ t : Tu, tup t = D.what₂.mu0 → (A.fam.R t).S.Good 1 → (∀ i j, (A.fam.R t).S.H i j ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ v : InfinitePlace D.what₂.LL, ((A.fam.R t).S.H.map v.embedding).PosDef) → (A.fam.R t).S.ActGood (A.fam.R t).r → (A.fam.R t).S.ActRat (A.fam.R t).r → GlobalTheory.Core.Target (GlobalTheory.Core.Rk.Mt D Am) := by
  intro D Gp _ _ Pl0 Tu m A Am P ψ tup jA J hT t ht hG hcm hpos hAG hAR
  obtain ⟨v0, hv0⟩ := GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩
  have hL := GlobalTheory.T.cm_level_hermitian_integral D.what₂.LL v0 hv0 (A.fam.R t).S hG hcm hpos Gp (A.fam.R t).r hAG hAR
    (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ
  have hU : DV.Used D (tup t) := Or.inl ht
  have key : GlobalTheory.Core.Target (Am.MtH (tup t)) := by
    intro hr
    refine GlobalTheory.T.muMaxDual_nonpos_of_dual_le D.what₂.LL (Formalism.DivisionValues.cmMax D.what₂.LL) (isCMSub_cmMax' D.what₂.LL) v0 hv0 (Am.MtH (tup t)) _
      (rH D A P ψ t) (J.eA t hU) (rNab D A P ψ t) (Am.MtH_good _ hU) hr hL.1 ?_ (hT.lat t hU) hL.2.2
    intro v i j
    rw [hT.metric t hU v (GlobalTheory.Core.AmbTieStep.posAt_of_posDef _ v (hL.2.1 v)), GlobalTheory.Core.AmbTieStep.hAt_single]
  show GlobalTheory.Core.Target (Am.MtH D.what₂.mu0)
  rw [← ht]
  exact key
end

