import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0139
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerate
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselSide_of_isType (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (u : ℕ → ℝ) (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hG : B.IsHaarOn (GG k r) μG) (hπ : Q.IsType k r z π u) :
    ∃ νq, SideG k r z π u μW μN μG νq := by
  have hW' := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 z hz hT hk).2 hW
  have hN' := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.2 hN
  have hG' := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μG).1.2 hG
  obtain ⟨νq, hν⟩ := GlobalTheory.T.exists_quotientMeasure_besselPeriodSubgroup_unitary k r z μW μN μG hz hT hW' hN' hG'
  exact ⟨νq, hz, hT, GlobalTheory.T.exists_harishChandraParam_of_typeOfUnitaryW k r Wp z π u hz hT hπ, hπ.2.2.2.2.2, hW', hN', hG', hν⟩

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegral
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem theta_series_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 →
    Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  intro d q hq M ω θ hd h16 hs hL hM hθ
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd h16 hs
  obtain ⟨α, hα, hα1, hα2⟩ := h4 1 1 (Nat.coprime_one_left q)
  obtain ⟨⟨a, ha⟩, ⟨m, hm⟩, -⟩ := h2 α hα
  have hq1 : (q : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    exact zpow_lt_one_of_neg₀ this (by norm_num)
  have hα1' : ‖M.ι α - 1‖ < 1 := by
    have := hα1.trans_lt hq1
    simpa using this
  have hn : ‖M.ι α‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := M.ι α - 1) (y := (1 : ℂ_[q]))
      (by rw [norm_one]; exact hα1'.ne)
    rw [sub_add_cancel, norm_one, max_eq_right hα1'.le] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hn
  have hmn : ‖(m : ℂ_[q])‖ < 1 := by
    have : (m : ℂ_[q]) = M.ι α * M.ι (conj α) := by
      rw [← map_mul, ← hm, map_natCast]
    rw [this, norm_mul, hn, one_mul]
    exact hα2.trans_lt hq1
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exfalso
      have : α * conj α = 0 := by rw [← hm]; simp
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    · simp at hmn
    · omega
  obtain ⟨ε, -, hεa, -, hεb, hfe, -⟩ := GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd h16 hs hL hM hθ α m hα hα0 hm
  obtain ⟨hmul, -⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨hb, hc0, hc1, -⟩ := hmul a
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul]
    have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
    rw [this, mul_zero]
  obtain ⟨hring, hconst, -, hcc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  have hθa : ∀ z, AnalyticAt ℂ θ z := fun z => hθ.1.analyticAt z
  have hpow : ∀ k : ℕ, hat M.ι (C ω * logS) (fun z => θ z ^ k) = hat M.ι (C ω * logS) θ ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have := (hring (fun z => θ z ^ k) θ ((hθa 0).pow k) (hθa 0)).2.1
      simp only [pow_succ]
      rw [this, ih]
  have hsub := (GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω θ (hθa 0)).2.2.1 α a ha
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
    (hθa 0).continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
  have hαa : AnalyticAt ℂ (fun z => θ (α * z)) 0 :=
    (hθ.1.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => α * z))).analyticAt 0
  have heq := (hring (fun z => θ (α * z)) (fun z => θ z ^ m * ε z) hαa (((hθa 0).pow m).mul hεa)).2.2.1
    ((hne.mono fun z hz => hfe z hz).filter_mono nhdsWithin_le_nhds)
  rw [hsub, (hring (fun z => θ z ^ m) ε ((hθa 0).pow m) hεa).2.1, hpow] at heq
  refine (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m hc0 (by rw [hc1, ← ha, hn]) hmn hm2).2 _ _ hb hεb ?_ heq
  rw [hcc, hθ.2.1, map_one]

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScalarOfRun

theorem ceil_toNat (x : ℝ) : ⌈x⌉.toNat = ⌈x⌉₊ := rfl

theorem barE_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem cP_of_mem_small (D : D7) (Tn : ℕ+) (N p : ℕ) (hp : p ∈ D.host.small) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP N p = ⌈(padicValNat p D.host.QS : ℝ) * (N : ℝ)⌉.toNat := by
  unfold DepPage.cP
  rw [if_pos (show (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p from Or.inl hp)]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉.toNat = _
  rw [GlobalTheory.RunDepth.vdOf, if_pos hp]

theorem cP_of_isRam_of_notMem_small (D : D7) (Tn : ℕ+) {j : ℕ} (w : WeightFamilies.Wt D j) (p : ℕ) (hp : p ∉ D.host.small)
    (hr : (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP (WeightAlgebra.DF w) p = Formalism.MainNotions.DIV.Cons.cHalf w := by
  unfold DepPage.cP
  rw [if_pos hr, ceil_toNat]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉₊ = _
  rw [GlobalTheory.RunDepth.vdOf, if_neg hp, Formalism.MainNotions.DIV.Cons.cHalf]
  congr 1; ring

theorem depth_page_first_zeta_factor_eq_prime_power (D : D7) (Tn : ℕ+) {j : ℕ} (wL wF : WeightFamilies.Wt D j) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) =
      pPow D (Tn * c2 D wL + c2 D wF) (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) := by
  have hq := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.q D.host.q_notMem_small (Or.inr (Or.inl rfl))
  have hd := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.d D.host.d_notMem_small (Or.inr (Or.inr rfl))
  have hS := UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow D.host.QS Tn (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) D.host.QS_pos.ne'
  unfold pPow c2
  rw [← hS]
  conv_rhs => enter [1, 2]; rw [← hq wL, ← hq wF]
  conv_rhs => enter [2]; rw [← hd wL, ← hd wF]
  unfold DepPage.Z1
  congr 2
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p ∈ D.host.small := (Finset.mem_filter.1 hp).1
  rw [cP_of_mem_small D Tn _ p hp', cP_of_mem_small D Tn _ p hp']
  rfl

theorem sigAt_eq_sigRec : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ), InR D j → HalfEX T.toCore EX → ∀ (K : Type) [Field K] [NumberField K] [Algebra (𝓞 D.host.E) K] (φ : T.Q.c.F →+* K), (∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) K x = φ ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F)) → sigAt (Dw := T.Q.Dw j) (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j = φ ((sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D L Pm Tp hK T h hinj EX j hj hE K _ _ _ φ hφ
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  let ψ : 𝓞 T.Q.c.F →+* K := φ.comp (algebraMap (𝓞 T.Q.c.F) T.Q.c.F)
  have hψ : ∀ x, algebraMap (𝓞 D.host.E) K x = ψ (iE D hinj (recB h.toLawsCore) x) := hφ
  let Tn : ℕ+ := ⟨Tp.TO, GlobalTheory.RunDepth.TO_pos Tp⟩
  have hnn : nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j =
      ψ (nnW (recB h.toLawsCore) hinj EX (kaR Tp hK j)) := by
    letI : StarRing (𝓞 D.host.E) := starRingOfComm
    refine (nnKAt_depDataOf T.toCore EX _ _ _ _ _ _ _ hM hE j).trans ?_
    refine Eq.trans ?_ (map_prod ψ _ _).symm
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [barE_eq_piBarO, hψ, hψ]
    exact ((map_mul ψ _ _).trans (congrArg₂ (· * ·) (map_pow ψ _ _) (map_pow ψ _ _))).symm
  have hL := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (lR Tp hK j)
  have hF := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (fR Tp hK j)
  have hn : (fR Tp hK j).n = 8 * D.R.f * D.R.r + 4 := Tp.nP_eq
  show nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j *
      (((D.host.g 0 * D.host.g 1 : ℕ) : K) ^ (D.R.f * D.R.r * (8 * D.R.f * D.R.r + 4)) *
        (((depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (lR Tp hK j)))
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (fR Tp hK j))) : ℕ) : K)) =
      ψ (sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
  rw [hnn, hL, hF, depth_page_first_zeta_factor_eq_prime_power, ← hn, ← Nat.cast_pow, ← Nat.cast_mul, ← map_natCast ψ, ← map_mul]
  rfl

end GlobalTheory.ScalarOfRun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslateStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_congruence_germ_integral_translate : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  first | exact @GlobalTheory.EigenGerm.eigen_germ | exact GlobalTheory.EigenGerm.eigen_germ | (intros; apply GlobalTheory.EigenGerm.eigen_germ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

noncomputable section

namespace GlobalTheory.PtTie

theorem emb_eq_of_inPsi {D : D7} {Q : Par D} (hp : Q.PinHost) {τ σ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ)
    (hσ : InPsi Q.H σ) {x : D.host.E} (hx : x ∈ D.host.K) : τ x = σ x := by
  have hs : τ D.host.sqrtMinusD = σ D.host.sqrtMinusD := by
    rw [← hp.2.1]; exact hτ.trans hσ.symm
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hs
  | algebraMap q => simp
  | add a b ha hb iha ihb => rw [map_add, map_add, iha ha, ihb hb]
  | inv a ha iha => rw [map_inv₀, map_inv₀, iha ha]
  | mul a b ha hb iha ihb => rw [map_mul, map_mul, iha ha, ihb hb]

theorem prod_pow_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {M : Type} [CommMonoid M] (F : (D.host.E →+* ℂ) → M) :
    ∏ τ : D.host.E →+* ℂ, F τ ^ (∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ))) =
      ∏ t : D.what₂.Tau, (F (DV.tauEmb D t) ^ (∑ i, w.aP t i) *
        F (ComplexEmbedding.conjugate (DV.tauEmb D t)) ^ (∑ i, w.aM t i)) := by
  classical
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [GlobalTheory.WeightExponents.wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.prod_congr rfl fun τ _ => by rw [hsw τ, ← Finset.prod_pow_eq_pow_sum], Finset.prod_comm]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [pow_add, pow_ite, pow_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 :=
    GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem emb_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.host.E →+* ℂ) :
    τ ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = starRingEnd ℂ (τ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  have h1 : ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = ((barE D (EX.piG i) : 𝓞 D.host.E) : D.host.E) := by
    rw [barE_eq_conj]; rfl
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj D.host.E τ _

theorem nrm_eq_prod {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    {τ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ) :
    nrm (Q.Dw j) Q.c (wtA w) (EX.piG 0 * EX.piG 1) =
      ∏ i : Fin 2, embK Q.c τ (EX.piG i) ^ Dplus w * embK Q.c τ (piBarO EX i) ^ Dminus w := by
  have h1 : ∀ t i, embK Q.c (DV.tauEmb D t) (EX.piG i) = embK Q.c τ (EX.piG i) := fun t i =>
    Subtype.ext (emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i))
  have h2 : ∀ t i, embK Q.c (ComplexEmbedding.conjugate (DV.tauEmb D t)) (EX.piG i) = embK Q.c τ (piBarO EX i) :=
    fun t i => Subtype.ext (by
      rw [embK_coe, embK_coe, emb_piBarO, ← emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i)]
      simp)
  unfold nrm Dplus Dminus
  rw [prod_pow_wtA hQ hj w fun σ => embK Q.c σ (EX.piG 0 * EX.piG 1)]
  simp only [map_mul, h1, h2]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Fin.prod_univ_two,
    mul_pow, mul_pow]
  ring

theorem map_nnW {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) :
    ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) = ∏ i : Fin 2, ((iE D hinj B (EX.piG i) : 𝓞 B.KO) : B.KO) ^ Dplus w *
      ((iE D hinj B (piBarO EX i) : 𝓞 B.KO) : B.KO) ^ Dminus w := by
  unfold nnW
  simp only [RingOfIntegers.coe_eq_algebraMap, map_prod, map_mul, map_pow]

theorem nrm_eq_nnW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j), nrm (T.Q.Dw j) T.Q.c (wtA w) (EX.piG 0 * EX.piG 1) = ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D T h j hj hinj EX w
  obtain ⟨τ, hτ, hE⟩ := exists_inPsi_iE_eq_embK D T h hinj
  rw [nrm_eq_prod h.pins hj EX w hτ]
  refine Eq.trans ?_ (map_nnW (recB h.toLawsCore) hinj EX w).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hE, ← hE]

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProofStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlaceDepthBound_proof : NuGoodSt := by
  first | exact @GlobalTheory.GoodDepth.nuGood | exact GlobalTheory.GoodDepth.nuGood | (intros; apply GlobalTheory.GoodDepth.nuGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NusOfEqRamMulNuStarAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.RunDepthScale

open Formalism.MainNotions.ModuliIntegralCharts.H1 in
theorem nusOf_eq_nuN {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (w : WeightFamilies.Wt D j)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : DepPage)
    (h1 : Q.g1 = D.host.g 0) (h2 : Q.g2 = D.host.g 1) (hq1 : Q.q1 = D.host.q) (hdd : Q.dd = D.host.d)
    (hsm : Q.sm = D.host.small) (hvd : Q.vd = vdOf D) :
    nusOf B w nu la = (ramOverZ la : ℝ) * Q.nuN (WeightAlgebra.DF w) (nu la) (resCharOf la) := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold nusOf DepPage.nuN
  rw [H1algLink.eWL_eq la, h1, h2]
  by_cases hc : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
  · rw [dif_pos hc]
    have hch := (H1algLink.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec hc)
    rw [← hch, mul_div_assoc]
    congr 1
    by_cases e0 : resCharOf la = D.host.g 0
    · rw [if_pos e0, e0]
    · rw [if_neg e0]
      have e1 : resCharOf la = D.host.g 1 := by
        generalize Classical.choose hc = i at hch
        fin_cases i
        · exact absurd hch e0
        · exact hch
      rw [if_pos e1, e1]
  · rw [dif_neg hc]
    have e0 : ¬ resCharOf la = D.host.g 0 := fun e =>
      hc ⟨0, (H1algLink.prime_mem_iff la (D.host.g_prime 0)).2 e⟩
    have e1 : ¬ resCharOf la = D.host.g 1 := fun e =>
      hc ⟨1, (H1algLink.prime_mem_iff la (D.host.g_prime 1)).2 e⟩
    rw [if_neg e0, if_neg e1]
    congr 2
    unfold DepPage.cP DepPage.IsRam
    rw [hq1, hdd, hvd, hsm, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
    have hS : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
      (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
    simp only [hS, H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd]
    by_cases a2 : resCharOf la ∈ D.host.small
    · rw [if_pos a2, if_pos (Or.inl a2)]
      unfold c2 vdOf
      rw [if_pos a2, Int.ceil_toNat, ← Nat.cast_mul, Nat.ceil_natCast]
    · rw [if_neg a2]
      by_cases b : resCharOf la = D.host.q ∨ resCharOf la = D.host.d
      · rw [if_pos b, if_pos (Or.inr b)]
        unfold Formalism.MainNotions.DIV.Cons.cHalf vdOf
        rw [if_neg a2, Int.ceil_toNat]
        congr 2
        ring
      · rw [if_neg b, if_neg (fun h => h.elim a2 b)]
        simp

theorem nusOf_eq_ram_mul_nuStarAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (EX : ErrX D) (j : ℕ), InR D j → letI := T.Q.H.starRing; ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nusOf (recB h.toLawsCore) (lR Tp hK j) (fun la' => (nuW (T.Q.Xo j) T.Q.c la' T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la' : ℝ)) la = (ramOverZ la : ℝ) * nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (depOf T.toCore EX Tp hK) la j := by
  intro D L Pm Tp hK T h EX j hj la
  letI := T.Q.H.starRing
  refine (nusOf_eq_nuN (recB h.toLawsCore) (lR Tp hK j) _ la (depOf T.toCore EX Tp hK).Q rfl rfl rfl rfl rfl rfl).trans ?_
  rw [← GlobalTheory.WeightExponents.DF_wtA h.pins hj (lR Tp hK j)]
  rfl

end GlobalTheory.RunDepthScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerateStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  first | exact @GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | exact GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | (intros; apply GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValueStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDepth_le_scaled_rule_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  first | exact @GlobalTheory.DepthRule.depth_le_scaled_value | exact GlobalTheory.DepthRule.depth_le_scaled_value | (intros; apply GlobalTheory.DepthRule.depth_le_scaled_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightExponents_embeddings_degree : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  first | exact @GlobalTheory.WeightExponents.weight_exponents | exact GlobalTheory.WeightExponents.weight_exponents | (intros; apply GlobalTheory.WeightExponents.weight_exponents <;> assumption)
end

