import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StdProp

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_sigR [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sigR R σ) := by
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  exact this

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem measurableSet_fibre [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] (c : R) :
    MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E | qR R σ J (X 0) = c} :=
  (isClosed_eq (continuous_qR R σ J) continuous_const).measurableSet

omit [FiniteDimensional F E] in
theorem smul_eq_lrAct {n : ℕ} (g : HA R σ J) :
    (fun X : Fin n → Fin M → R ⊗[F] E => g • X) = lrAct (HA.mat R σ J g).val 1 := by
  funext X a
  show (HA.mat R σ J g).val.mulVec (X a) = _
  simp [lrAct, Matrix.one_apply]

end Local

theorem stdX_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b s M J x β ν hJ hβ hx ⟨mi, mv, hi, hv, hP⟩
  obtain ⟨nI, nV⟩ := nice_ainf_fv F
  obtain ⟨qloc, gloc⟩ := q_and_unitary_local_components F E σ M J
  have hβu : IsUnit β := Ne.isUnit hβ
  have bI := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Ainf F) nI M J _ _ _ mi s.haar_nuI (hβu.map _) hi
  have bV := fun v => GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Fv F v) (nV v) M J _ _ _ (mv v) (s.haar_nuV v)
    (hβu.map _) (hv v)
  have pI := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) nI M J x β _ _ mi hJ hβ hx s.haar_lamI s.haar_nuI hi
  have pV := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (nV v) M J x β _ _ (mv v) hJ hβ hx
    (s.haar_lamV v) (s.haar_nuV v) (hv v)
  obtain ⟨hfin, hne, huniq, hsupp⟩ := GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hP
  have h1 : ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 := by
    have := hsupp {X | qR (Ainf F) σ J (X 0) = algebraMap F _ β}
      (fun v => {X | qR (Fv F v) σ J (X 0) = algebraMap F _ β})
      (measurableSet_fibre _ σ J _) (fun v => measurableSet_fibre _ σ J _) bI.1 (fun v => (bV v).1)
    refine measure_mono_null (fun X hX => ?_) this
    exact fun h => hX ((qloc (X 0) β).2 h)
  refine ⟨h1, ?_, ?_, hfin, hne pI.2.2 fun v => (pV v).2.2⟩
  · intro g
    obtain ⟨⟨gi, hgi⟩, hgv⟩ := gloc g
    have hT := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν mi mv (HA.mat (AF F) σ J g) 1 hP
    have e1 : mi.map (lrAct ((HA.mat (AF F) σ J g).val.map prInf)
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map prInf)) = mi := by
      rw [← hgi, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact pI.1 gi
    have e2 : (fun v => (mv v).map (lrAct ((HA.mat (AF F) σ J g).val.map (prV v))
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map (prV v)))) = mv := by
      funext v
      obtain ⟨gv, hgv⟩ := hgv v
      rw [← hgv, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact (pV v).1 gv
    rw [e1, e2, Units.val_one, ← smul_eq_lrAct] at hT
    exact huniq _ hT
  · refine measure_mono_null (fun X hX => ?_) h1
    exact fun h => hX (GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM M J x β hJ hβ hx X h)

end GlobalTheory.GaugeEx.StdProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRepsOpen

open Filter Topology

theorem tendsto_smul_zero_of_compact {R M : Type} [Zero R] [Zero M] [SMulWithZero R M] [TopologicalSpace R]
    [TopologicalSpace M] [ContinuousSMul R M] {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) {C : Set M} (hC : IsCompact C)
    {y : ℕ → M} (hy : ∀ n, y n ∈ C) : Tendsto (fun n => a n • y n) atTop (𝓝 0) := by
  intro U hU
  have h : ∀ᶠ r in 𝓝 (0 : R), ∀ z ∈ C, r • z ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    refine (continuous_smul (M := R) (X := M)).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  exact (ha.eventually h).mono fun n hn => hn _ (hy n)

theorem tendsto_one_of_cong (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) (A : ℕ → Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hA : ∀ n : ℕ, ∀ z ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)), ∃ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)),
      A n *ᵥ z - z = n.factorial • y) : Tendsto A atTop (𝓝 1) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat F E L hL
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  obtain ⟨d, hd, hdL⟩ := GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  have h1 : (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hz : (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL, rfl⟩
  choose y hy e using fun n => hA n _ hz
  have ht := tendsto_smul_zero_of_compact (R := GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F) hC
    fun n => hLC _ (hy n)
  have ht' := ((tendsto_pi_nhds.1 ht i).mul_const ((1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((d : E)⁻¹))).add_const
    ((1 : Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j)
  rw [Pi.zero_apply, zero_mul, zero_add] at ht'
  refine ht'.congr fun n => ?_
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have e' : (A n - 1) *ᵥ (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) = n.factorial • y n := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e]
  rw [Nat.cast_smul_eq_nsmul, ← e', ← eq_sub_iff_add_eq, ← Matrix.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem exists_finCong_le (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (hJ : IsOpen (J : Set (Bridge.Gf V))) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → fin V k ∈ J := by
  by_contra hc
  have hc' : ∀ n : ℕ, ∃ k : GA D V, GlobalTheory.Member.FinCong V n.factorial k ∧ fin V k ∉ J := fun n => by
    by_contra h
    exact hc ⟨n.factorial, n.factorial_pos, fun k hk => by_contra fun h' => h ⟨k, hk, h'⟩⟩
  choose k hk hkJ using hc'
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key : ∀ u : ℕ → GA D V, (∀ n : ℕ, GlobalTheory.Member.FinCong V n.factorial (u n)) →
      Tendsto (fun n => (finHom V (u n)).1) atTop (𝓝 1) := fun u hu => by
    refine tendsto_one_of_cong D.host.F D.host.E _ h3 h4 _ fun n => ?_
    have := hu n
    unfold GlobalTheory.Member.FinCong at this
    rw [h1] at this
    exact this
  have ht : Tendsto (fun n => fin V (k n)) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine (key k hk).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
    have := key (fun n => (k n)⁻¹) fun n => GlobalTheory.Member.PrincLevel.finCong_inv (hk n)
    simp only [map_inv] at this
    exact this
  obtain ⟨n, hn⟩ := (ht.eventually (hJ.mem_nhds J.one_mem)).exists
  exact hkJ n hn

theorem exists_rep_splitOffBad : ∀ (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (bad : ℕ), bad ≠ 0 → IsOpen (J : Set (Bridge.Gf V)) → ∀ x : Bridge.Gf V, ∃ (γ : GQ V) (h : GA D V) (k : J), SplitOffBad V bad h ∧ x = Bridge.ratF V γ * fin V h * (k : Bridge.Gf V) := by
  intro D V J bad hb hJ x
  obtain ⟨N, hN, hK⟩ := exists_finCong_le D V J hJ
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V hN (fun k _ hk => hK k hk) (Nat.pos_of_ne_zero hb) x
  exact ⟨γ, h, k, GlobalTheory.SplitReps.splitOffBad_of_suppSplit V bad h hh hs, e⟩

end GlobalTheory.SplitRepsOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairInfTypes

theorem hasInfQ_tauE (D : D7) {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) (fun τ => a (D.eTau τ)) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Fintype.prod_equiv D.eTau _ _ fun _ => rfl).symm

theorem infTypesAt : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  intro D T L μ0 hL i t τ
  have h1 : HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 i) (hasInfQ_tauE D (L.C.isMu0 i).inf) τ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (hasInfQ_tauE D (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 : HasInfExp D (L.xi t) τ 0 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t) ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
    rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
    simp
  have h4 : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h3
    rw [add_zero] at h
    exact h
  refine ⟨h4, h2, h4, ?_⟩
  rw [sub_eq_add_neg]
  exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul h4 (GlobalTheory.Mem.HeckeExp.hasInfExp_inv h2)

end GlobalTheory.PairInfTypes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

def TwistConeVanishing {X : Scheme.{0}} (A N : LB X) (F : X.Modules) : Prop :=
  ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p →
    Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolumeStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  first | exact @GlobalTheory.Mem.Vol.volIs_trueVol | exact GlobalTheory.Mem.Vol.volIs_trueVol | (intros; apply GlobalTheory.Mem.Vol.volIs_trueVol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraicStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → Even a → Even b → (ambOf s B χ cD).ESmooth a b ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ), JetAlg (ambOf s B χ cD) a b S M := by
  first | exact @GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | exact GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | (intros; apply GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg <;> assumption)
end

