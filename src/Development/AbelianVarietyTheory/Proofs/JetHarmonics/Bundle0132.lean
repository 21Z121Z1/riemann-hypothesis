import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AutomorphicArithmetic.CMTraceForms.SplitPlacesDiscriminantDepthOfSplitAt
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormEqZeroOfDiagExp
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagExpZero

open GlobalTheory.FrameTwistCompare (lin quad)
open MvPowerSeries (constantCoeff pderiv)

section Flat

variable {S : Type} [CommRing S] {σ : Type}

def Flat (f : MvPowerSeries σ S) : Prop := constantCoeff f = 1 ∧ ∀ v, lin v f = 0

theorem flat_one : Flat (1 : MvPowerSeries σ S) := ⟨map_one _, fun v => by simp [lin]⟩

theorem quad_one (v w : σ) : quad v w (1 : MvPowerSeries σ S) = 0 := by simp [quad]

theorem Flat.mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) : Flat (f * g) := by
  refine ⟨by rw [map_mul, hf.1, hg.1, _root_.mul_one], fun v => ?_⟩
  have h1 := hf.2 v
  have h2 := hg.2 v
  unfold lin at h1 h2 ⊢
  simp [Derivation.leibniz, h1, h2]

theorem Flat.quad_mul {f g : MvPowerSeries σ S} (hf : Flat f) (hg : Flat g) (v w : σ) :
    quad v w (f * g) = quad v w f + quad v w g := by
  have h1 := hf.2 v
  have h2 := hg.2 v
  have h3 := hf.2 w
  have h4 := hg.2 w
  unfold lin at h1 h2 h3 h4
  simp [quad, Derivation.leibniz, h1, h2, h3, h4, hf.1, hg.1, add_comm]

theorem Flat.pow {f : MvPowerSeries σ S} (hf : Flat f) (q : ℕ) :
    Flat (f ^ q) ∧ ∀ v w, quad v w (f ^ q) = q * quad v w f := by
  induction q with
  | zero => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | succ q ih =>
    refine ⟨by rw [pow_succ]; exact ih.1.mul hf, fun v w => ?_⟩
    rw [pow_succ, ih.1.quad_mul hf, ih.2]
    push_cast
    ring

theorem flat_finprod {J : Type} (s : Finset J) {f : J → MvPowerSeries σ S} (hf : ∀ i, Flat (f i)) :
    Flat (∏ i ∈ s, f i) ∧ ∀ v w, quad v w (∏ i ∈ s, f i) = ∑ i ∈ s, quad v w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using flat_one, fun v w => by simp [quad_one]⟩
  | insert a s ha ih =>
    refine ⟨by rw [Finset.prod_insert ha]; exact (hf a).mul ih.1, fun v w => ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (hf a).quad_mul ih.1, ih.2]

theorem quad_eq_zero {f : MvPowerSeries σ S}
    (h : ∀ e : σ →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e (f - 1) = 0) (v w : σ) : quad v w f = 0 := by
  have h1 : quad v w (f - 1) = 0 := by
    simp only [quad, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    rw [h _ (by simp)]
    simp
  simpa [quad] using h1

end Flat

open GlobalTheory.FrameTwistCompare in
theorem flat_ev_twist {S : Type} [CommRing S] [Algebra ℚ S] {n d : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S)
    {a : Fin 2 → Pt S n d} (ha : TB.LogPf.CZ a) : Flat (ev a (expP (-bilL G c))) := by
  refine ⟨cc_ev_twist G c ha, fun v => ?_⟩
  have h0 := cc_comp1_log G (ha 0)
  have h1 := cc_comp1_log G (ha 1)
  rw [ev_expP G c ha, ev_bilL_eq G c ha, bilLog_eq_bil, lin_exp]
  · have := lin_bil (c := c) h0 h1 v
    unfold lin at this ⊢
    rw [map_neg, map_neg, this, neg_zero]
  · rw [map_neg, cc_bil h0, neg_zero]

theorem form_eq_zero_of_diag_exp : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (d : ℕ) (G : FGLaw S d) (w w' : Pt S 1 d), (∀ i, MvPowerSeries.constantCoeff (w i) = 0) → dLin w + dLin w' = 1 → ∀ c : Fin d → Fin d → S, (∀ i j, c i j = c j i) → Matrix.transpose (dLin w) * Matrix.of c = Matrix.of c * dLin w' → ∀ (n q : ℕ), 1 ≤ n → 1 ≤ q → (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ 2 → MvPowerSeries.coeff e ((∏ i : Fin n, ev (n := n) ![pt S d i, comp1 w (pt S d i)] (expP (-bilL G c)) ^ q) - 1) = 0) → c = 0 := by
  intro S _ _ d G w w' hw hsum c hsym hbal n q hn hq h
  have hz : ∀ i : Fin n, TB.LogPf.CZ (![pt S d i, comp1 w (pt S d i)] : Fin 2 → Pt S n d) := by
    intro i j k
    fin_cases j
    · exact FrameTwistCompare.cc_pt i k
    · exact TB.WickVanishing.cc_comp1 _ _ hw (FrameTwistCompare.cc_pt i) k
  have hfl := fun i => flat_ev_twist G c (hz i)
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hu : IsUnit (q : S) := by
    have := (IsUnit.mk0 (q : ℚ) (by exact_mod_cast (by omega : q ≠ 0))).map (algebraMap ℚ S)
    rwa [map_natCast] at this
  have key : ∀ a b, (Matrix.of c * dLin w) a b + (Matrix.of c * dLin w) b a = 0 := by
    intro a b
    have h2 := quad_eq_zero h (i₀, a) (i₀, b)
    rw [(flat_finprod _ fun i => ((hfl i).pow q).1).2, Finset.sum_eq_single i₀, ((hfl i₀).pow q).2,
      hu.mul_right_eq_zero, FrameTwistCompare.quad_ev_twist G c (hz i₀), neg_eq_zero] at h2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        FrameTwistCompare.lin_comp1 _ (FrameTwistCompare.cc_pt _), FrameTwistCompare.lin_pt] at h2
      simp only [Matrix.mul_apply, Matrix.of_apply]
      simpa [mul_add, Finset.sum_add_distrib] using h2
    · intro i _ hi
      rw [((hfl i).pow q).2, FrameTwistCompare.quad_ev_twist G c (hz i)]
      simp [FrameTwistCompare.lin_pt, hi.symm]
    · simp
  have ht : (Matrix.of c).transpose = Matrix.of c := Matrix.ext fun i j => hsym j i
  have h3 : Matrix.of c * dLin w + Matrix.of c * dLin w' = 0 := by
    rw [← hbal]
    have e : (dLin w).transpose * Matrix.of c = (Matrix.of c * dLin w).transpose := by
      rw [Matrix.transpose_mul, ht]
    rw [e]
    exact Matrix.ext fun a b => key a b
  rw [← Matrix.mul_add, hsum, Matrix.mul_one] at h3
  exact h3

end GlobalTheory.DiagExpZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KerPow GlobalTheory.IndefiniteRowSideFullHecke.TwistedPoints
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistCompare

section Basis

variable {A : Type} [CommRing A] {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

end Basis

section Hyp

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

end Hyp

section Conclusion

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R)

end Conclusion

theorem cube : Out.CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen GlobalTheory.laws_without_cohomology.1 (GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1
        GlobalTheory.KuennethOne.kuenneth_injective)))

theorem exists_degPre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) :
    ∃ (D : Out.DegPre R) (α : D.X) (e : D.P = P), e ▸ D.c α = c := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  choose psi hpsi using fun n : ℤ => DVR.exists_gen_of_local (V := FractionRing R) P.L P.isLB (K := PUnit)
    (fun _ => Out.ptK (c ^ n)) (fun _ => -1)
  exact ⟨{ P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := ℤ
           c := fun n => c ^ n, c_add := fun a b => zpow_add c a b, psi := psi, psi_gen := hpsi },
    (1 : ℤ), rfl, zpow_one c⟩

end GlobalTheory.TwistCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HostFieldTwoConjugatePlacesOverTwo
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.CharDepth

theorem twoPlaces_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), H.d = D.host.d → ∀ (p : ℕ) [Fact p.Prime], p ∈ D.host.small → UpperTheory.Depth.SplitAt H.d p ∧ UpperTheory.Depth.SplitPlaces p H D.R.f (D.host.vdH p) ∧ 0 ≤ D.host.vdH p ∧ D.host.vdH p ≤ vd2 D := by
  intro D H hd p _ hp
  have hpp : p.Prime := Fact.out
  have hs : UpperTheory.Depth.SplitAt H.d p := by
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr (by rw [hd]; exact D.host.QS_split p hpp h2 (D.host.mem_small_iff.1 hp).2)
  obtain ⟨h1, -, -, -, h5⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  refine ⟨hs, ?_, D.host.vdH_nonneg p, (h1 p hp).1.trans (h1 p hp).2⟩
  rw [h5 p]
  exact UpperTheory.splitPlaces_discriminantDepth_of_splitAt p D.host.E H hs D.R.f D.host.finrank_E'

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.WeightRows

theorem kappa_entries_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ τ : D.what₂.Tau, (∀ i, i.1 < D.R.k - 1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ wj D j τ + L.Sc) ∧ (∀ i, D.R.k - 1 ≤ i.1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ L.etaSz) ∧ ∀ i, ((kaR Tp hK j).aM τ i : ℝ) ≤ L.etaSz := by
  intro D L Pm Tp hK j hj τ
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have a9 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have big : ∀ i : Fin (D.R.sigW j).1, ((kaR Tp hK j).aP τ i : ℝ) ≤
      ((DV.sigPar D τ i : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    have hi : i.1 < D.R.k + j - 1 := i.2
    have hi' : i.1 + 2 ≤ D.R.k + j := by omega
    have hr : (i.1 : ℝ) + 2 ≤ D.R.k + j := by exact_mod_cast hi'
    have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).1 i
    rw [← e1, DV.aPlusQ_eq] at e2
    unfold DV.eQ at e2
    rw [dif_pos ⟨h1, h2⟩] at e2
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at e3
    unfold kaR
    linarith
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_⟩
  · have b := big i
    unfold DV.sigPar at b
    rw [dif_pos hi] at b
    have a1 := (L.cloud_v τ ⟨i.1, hi⟩).2
    unfold wj
    rw [dif_pos (by omega : j - 1 < D.R.m)]
    linarith
  · have b := big i
    have hi2 : i.1 < D.R.k + j - 1 := i.2
    have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
    unfold DV.sigPar at b
    rw [dif_neg (by omega), dif_pos hb] at b
    have a2 := (abs_le.1 (L.be_close τ ⟨i.1 - (D.R.k - 1), hb⟩ ⟨j - 1, by omega⟩)).1
    push_cast at a2 b
    linarith
  · have hs : (D.R.sigW j).2 = D.R.m - j := rfl
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have hi := (Fin.rev i).2
    unfold DV.aMinusQ DV.eQ at e2
    rw [dif_pos (by omega), dif_pos ⟨h1, h2⟩] at e2
    have a2 := (abs_le.1 (L.be_close τ ⟨j + (Fin.rev i).1, by omega⟩ ⟨j - 1, by omega⟩)).2
    have a8 : (0 : ℝ) ≤ (Fin.rev i).1 := Nat.cast_nonneg _
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    have e4 := congrArg (fun q : ℤ => (q : ℝ)) e1
    push_cast at e3 e4 a2
    unfold kaR
    linarith

end GlobalTheory.WeightRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem mul_toNat_fdiv_le (T d : ℕ) (c x : ℤ) (hc : 0 ≤ c) (hx : x ≤ c + 2) :
    (T : ℤ) * ((Int.fdiv x ((T + d + 2 : ℕ) : ℤ)).toNat : ℤ) ≤ c := by
  have hpos : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ) := by positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hpos.le]
  have h1 := Int.ediv_mul_le x hpos.ne'
  generalize x / ((T + d + 2 : ℕ) : ℤ) = q at h1
  rcases le_or_gt q 0 with hq | hq
  · rw [Int.toNat_eq_zero.2 hq]; simpa using hc
  · rw [Int.toNat_of_nonneg hq.le]
    push_cast at h1
    have hd : (0 : ℤ) ≤ d := by positivity
    nlinarith [mul_nonneg hq.le hd]

theorem gapZ_nonneg_of_antitone {p : ℕ} {a : Fin p → ℕ} (ha : Antitone a) (i : Fin p) :
    0 ≤ WeightAlgebra.gapZ a i := by
  unfold WeightAlgebra.gapZ
  split_ifs with h
  · have : a ⟨i.1 + 1, h⟩ ≤ a i := ha (by simp [Fin.le_def])
    omega
  · positivity

theorem mul_ofGaps_le {p : ℕ} (T : ℕ) (g a : Fin p → ℕ)
    (h : ∀ i, (T : ℤ) * (g i : ℤ) ≤ WeightAlgebra.gapZ a i) (i : Fin p) : T * ofGaps g i ≤ a i := by
  have key : ∀ n : ℕ, ∀ i : Fin p, i.1 + n + 1 = p → T * ofGaps g i ≤ a i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hn : ¬ i.1 + 1 < p := by omega
      have h1 := h i
      rw [ofGaps_last g i hn]
      unfold WeightAlgebra.gapZ at h1
      rw [dif_neg hn] at h1
      exact_mod_cast h1
    | succ n ih =>
      intro i hi
      have hn : i.1 + 1 < p := by omega
      have h1 := h i
      have h2 := ih ⟨i.1 + 1, hn⟩ (by simp only; omega)
      rw [ofGaps_succ g i hn, Nat.mul_add]
      unfold WeightAlgebra.gapZ at h1
      rw [dif_pos hn] at h1
      have h3 : ((T * g i : ℕ) : ℤ) ≤ (a i : ℤ) - a ⟨i.1 + 1, hn⟩ := by push_cast; exact h1
      omega
  exact key (p - 1 - i.1) i (by have := i.2; omega)

theorem mul_lWt_aP_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : T * (lWt D ka T nW hW).aP τ i ≤ ka.aP τ i := by
  refine mul_ofGaps_le T (lGapP D ka T nW τ) (ka.aP τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aPlus_antitone τ) i
  unfold lGapP WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    have : (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * nW := by positivity
    have : (0 : ℤ) ≤ (D.R.r : ℤ) := by positivity
    linarith

theorem mul_lWt_aM_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) : T * (lWt D ka T nW hW).aM τ i ≤ ka.aM τ i := by
  refine mul_ofGaps_le T (lGapM D ka T τ) (ka.aM τ) (fun i => ?_) i
  have h0 := gapZ_nonneg_of_antitone (ka.aM_anti τ) i
  unfold lGapM WeightAlgebra.Tp
  split_ifs with h
  · exact mul_toNat_fdiv_le _ _ _ _ h0 le_rfl
  · refine mul_toNat_fdiv_le _ _ _ _ h0 ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    linarith

theorem mul_DF_lWt_le (D : D7) {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW) :
    T * WeightAlgebra.DF (lWt D ka T nW hW) ≤ WeightAlgebra.DF ka := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
  exact Nat.add_le_add (Finset.sum_le_sum fun i _ => mul_lWt_aP_le D ka T nW hW τ i)
    (Finset.sum_le_sum fun i _ => mul_lWt_aM_le D ka T nW hW τ i)

theorem mul_rows_lR_le_kaR : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ) (τ : D.what₂.Tau), (∀ i, Tp.TO * (lR Tp hK j).aP τ i ≤ (kaR Tp hK j).aP τ i) ∧ (∀ i, Tp.TO * (lR Tp hK j).aM τ i ≤ (kaR Tp hK j).aM τ i) ∧ Tp.TO * WeightAlgebra.DF (lR Tp hK j) ≤ WeightAlgebra.DF (kaR Tp hK j) := by
  intro D L Pm Tp hK j τ
  exact ⟨fun i => mul_lWt_aP_le D _ _ _ _ τ i, fun i => mul_lWt_aM_le D _ _ _ _ τ i,
    mul_DF_lWt_le D _ _ _ _⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlaceStatement
section
open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onObj_exponent_eq_rounded_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  first | exact @GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | exact GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | (intros; apply GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem not_dvd_discr_host : ∀ (Rk : Ranks) (H : Formalism.BasicNotions.Host Rk) (p : ℕ), p.Prime → p ∉ H.small →
    p ≠ H.q → p ≠ H.d → ¬ (p : ℤ) ∣ NumberField.discr H.E := by
  intro Rk H p hp hs hq hd hdvd
  have hc : p ∣ H.QS * H.q * H.d := H.der.discr_primes.1 p hp hdvd
  rcases (hp.dvd_mul).1 hc with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact hs (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
    · exact hq ((Nat.prime_dvd_prime_iff_eq hp H.hyp.1).1 h)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).1 h)

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevel
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem resChar_sub_one_le_ramOverZ_of_primitiveRoot {L : Type} [Field L] [NumberField L]
    (la : HeightOneSpectrum (𝓞 L)) (ζ : L) (hζ : IsPrimitiveRoot ζ (resCharOf la)) :
    resCharOf la - 1 ≤ ramOverZ la := by
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hpP := Formalism.L2.Pj.Crude.crv_char_mem la
  unfold ramOverZ
  generalize resCharOf la = p at hp hpP hζ ⊢
  have hP := la.isPrime
  have : Fact p.Prime := ⟨hp⟩
  set Z : 𝓞 L := ⟨ζ, hζ.isIntegral hp.pos⟩ with hZdef
  have hZ : IsPrimitiveRoot Z p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hassoc : Associated ((Z - 1) ^ (p - 1)) (p : 𝓞 L) := by
    have h2 : (Polynomial.cyclotomic p (𝓞 L)).eval 1 = p := Polynomial.eval_one_cyclotomic_prime
    rw [← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← Nat.totient_prime hp, ← hZ.card_primitiveRoots, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun η hη => ?_
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨i, -, hi, rfl⟩ := hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    simpa using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
  have hZP : Z - 1 ∈ la.asIdeal := by
    obtain ⟨u, hu⟩ := hassoc.symm
    exact hP.mem_of_pow_mem _ (hu ▸ la.asIdeal.mul_mem_right _ hpP)
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.span {(p : 𝓞 L)} ≤ la.asIdeal ^ (p - 1) := by
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem la.asIdeal).mpr hZP) _
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hne hP]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
  · rw [Ideal.dvd_iff_le, hmap]
    exact hle

theorem resChar_sub_one_le_ramOverZ_of_dvd_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l)
      (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  intro E _ _ _ H l c la hd
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hmem := Formalism.L2.Pj.zeta_mem_of_dvd c (hd.trans (Nat.dvd_lcm_left l.M l.A)) h0
  refine resChar_sub_one_le_ramOverZ_of_primitiveRoot la ⟨_, hmem⟩ ?_
  exact IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp _ hp.ne_zero) Subtype.val_injective

end GlobalTheory.RunDepth
end

