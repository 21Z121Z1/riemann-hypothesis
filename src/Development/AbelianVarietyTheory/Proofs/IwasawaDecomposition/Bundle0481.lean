import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0474
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicity
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.ThetaMap

open GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

variable {D : D7}

open Classical in

theorem restrictsTo_of_eq {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    {U : KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) : RestrictsTo M T U := by
  intro v
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT.equiv τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem exists_extension (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} (hM : HolShape M) {w : D.what₂.Tau → Fin V.rank → ℤ} (hw : WtIs M w)
    {J : Set (GA D V)} (hJ : J ⊆ (GfC V : Set (GA D V))) {χ : GA D V → ℂ} {U : KMap M} (ha : ∀ e, IsAutFun V (U e))
    (hl : ∀ e, ∀ k ∈ J, ∀ g, U e (g * k) = χ k * U e g) (hs : ∀ e, IsSmoothFn V θ (U e))
    (hg : ∀ e, IsUnifModGrowth V θ (U e)) (hz : ∀ e, ZCusp V (U e)) (hk : KEquiv θ M U)
    (hh : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) :
    ∃ T : MMap M, IsMultMap θ M J χ T ∧ RestrictsTo M T U := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible D V S M hM
  obtain ⟨v, hv⟩ := exists_isExtVec M h1
  let e : ∀ τ, lowT M τ := fun τ => ⟨v τ, (hv τ).2.1⟩
  have he : ∀ τ, e τ ≠ 0 := fun τ h0 => by
    have h3 : v τ = 0 := congrArg Subtype.val h0
    have := (hv τ).1
    rw [h3] at this
    simp at this
  have hfin : ∃ μ 𝓕, FinPair V μ 𝓕 := by
    obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
    have : IsTopologicalGroup (GA D V) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨hr, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ
    exact ⟨_, 𝓕, hμ, hr, h𝓕, (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V _ 𝓕 ⟨hμ, h𝓕⟩).2⟩
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hθ hM hw hv hfin J χ (U e) hJ
    ⟨ha e, GlobalTheory.T.bounded_of_smooth_cuspidal_uniform_moderate hP D θ V hθ _ (ha e) (hs e) (hg e) (GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (ha e) (hz e)), hl e,
      GlobalTheory.T.holomorphicType_at_extremal_of_kEquivariant_loweringKilled D θ V S M w hθ hM hw h1 h2 U hs hk hh e hv⟩ (hz e)
  exact ⟨T, hT, restrictsTo_of_eq h1 h2 hT hk e he hTe⟩

open Classical in

theorem exists_member (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {θ : InfFam D} (hθ : IsInfFam θ) (hpos : ∀ τ, (gramAt D S τ).PosDef)
    {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp} (hM : HolShape M) {w : D.what₂.Tau → Fin T.rank → ℤ} (hw : WtIs M w)
    {c : CoefA S} (hc : c.Is) (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {Δ : PolF D T.rank S.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank}
    (hio : IsIoW θ M c om (fun P => pt P) Δ io)
    (hΔ : ∀ τ, ∀ Z ∈ pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0)
    {J : Set (GA D T)} (hJ : J ⊆ (GfC T : Set (GA D T)))
    (hJo : ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → k ∈ J)
    (hfix : ∀ k ∈ J, ∀ P, om (1, k) (pt P) = pt P) {χ : GA D T → ℂ} (hχ : ∀ k, χ k = 1)
    (hsupp : ∀ P h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D,
      ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (pt P)) = 0)
    {F : GA D S → c.W} (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ Θ : MMap M, IsMultMap θ M J χ Θ ∧ ∀ v : ∀ ρ, lowT M ρ,
      Θ (fun ρ => (v ρ : M.sm ρ)) = lift om ν 𝓕 fun h => pt (io (PiTensorProduct.tprod ℂ v) (F h)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible D T Sp M hM
  have hint : ∀ e g, IntegrableOn (fun h => thetaKO om h g (pt (io e (F h)))) 𝓕 ν := fun e g =>
    GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io e)
      (fun _ => hpt _) _ hF hFi ν 𝓕 hν h𝓕 g
  let U₀ : LowT M →ₗ[ℂ] (GA D T → ℂ) :=
    { toFun := fun e => lift om ν 𝓕 fun h => pt (io e (F h))
      map_add' := fun e e' => by
        funext g
        simp only [lift, thetaKO, map_add, LinearMap.add_apply, Pi.add_apply]
        exact integral_add (hint e g) (hint e' g)
      map_smul' := fun a e => by
        funext g
        simp only [lift, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul a _ }
  let U : KMap M := U₀.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hU : ∀ v, U v = lift om ν 𝓕 fun h => (pt ∘ₗ io (PiTensorProduct.tprod ℂ v)) (F h) := fun _ => rfl
  have hmul : ∀ h g k φ, thetaKO om h (g * k) φ = thetaKO om h g (om (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hlev : ∀ v, ∀ k ∈ J, ∀ g, U v (g * k) = U v g := fun v k hk g => by
    simp only [hU, lift, hmul, LinearMap.comp_apply, hfix k hk]
  have hd := fun v => GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hs := fun v => GlobalTheory.T.thetaLift_definite_smooth_moderate_growth_annihilated D ψ S T χS χT om hom θ hθ hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕
  have hz := fun v => GlobalTheory.T.thetaLift_definite_constantTerm_eq_zero D ψ S T χS χT om hom hpos c.W (pt ∘ₗ io (PiTensorProduct.tprod ℂ v))
    (fun _ => hpt _) F hF hFi ν 𝓕 hν h𝓕 fun x h g ξ hξ => hsupp _ h g ξ hξ
  obtain ⟨O, hO, hOJ⟩ := hJo
  exact exists_extension hP hθ hM hw hJ (U := U)
    (fun v => ⟨(hd v).1.2, ⟨O, hO, fun k hk hk' => hlev v k (hOJ k hk hk')⟩, (hd v).1.1⟩)
    (fun v k hk g => by rw [hχ, one_mul, hlev v k hk]) (fun v => (hs v).1) (fun v => (hs v).2.1) hz
    (fun τ k hk v u hu => by
      funext g
      simp only [hU, lift, rTr, hmul, LinearMap.comp_apply, hio.2.1 τ k hk v u hu])
    fun τ Z hZ v => (hs v).2.2 τ Z fun x h =>
      GlobalTheory.T.lowestKType_values_killed_by_loweringPart D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v x h

theorem level_open (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ levS V β L := by
  classical
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  refine ⟨(lev D.sp.cm V.gram β L).comap (Lev.finE V), Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, fun k hk hk' => ⟨hk', hk⟩⟩
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem pureTensorO_one {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} sS sT BS BT (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have : (1 : PolF D T.rank S.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  rw [this, pureTensorO, pureTensorL, Module.Basis.constr_basis]
  simp [opPow]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem firesAt (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (h0 : R.toLevCh.Is A.μ0) (hm : R.IsModels)
    (hω : R.thP_ωP) (hv : R.thP_vP) (hp : R.thP_pt_theta) (hio : R.thP_ioP) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring.FiresAt R i t x := by
  have hx : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hm.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t => by
    have := hp i t 1
    rwa [RealDat.ptP, pureTensorO_one] at this
  obtain ⟨hM, w, hw⟩ := GlobalTheory.T.forms_model_holomorphic_integral_extremal_weight D G Pl0 T A Ks R hm.order i
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ (Vc D i).rank := fun τ => by
    have e := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e' := rank_Wc i
    have := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e
    omega
  have hΔ := fun τ => GlobalTheory.T.fockVector_mixedLaplacianKilled_loweringKilled D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hω i t) R.θ hm.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) _ (R.MW i (sg0 D A)) (fun τ => ((Wc D i).sig (tauE D τ)).1) (hm.order i) (R.vP i t) (hth i t)
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth i t)) (RealDat.Delta i) τ
    (GlobalTheory.T.mixed_laplacian_kills_product_of_minors D _ _ _ _ _ _ hpq τ)
  have key := exists_member hP (hω i t) hm.inf hpos hM hw (hm.cV i)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (hio i t) hΔ (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1)
    (level_open _ _ _) (fun k hk P => by
      rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ _ (hω i t) R.θ hm.inf 1 (one_mem _) k hk.1 _ _ _ _ _ P (hth i t),
        GlobalTheory.T.weilFiniteVector_fixed_principalLevel_coeffSpace D G Pl0 T A Ks R h0 hω hv hth i t k hk])
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i) (GlobalTheory.T.fock_vectors_killed_heisenberg_average_isotropic D G Pl0 T A Ks R h0 hm.inf hω hv hp i t)
    (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) _ _ hx) (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx)
    (hm.νV i t).1.1 (hm.νV i t).2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨fun e g => ?_, Θ, Submodule.subset_span hΘ, hΘv⟩
  exact GlobalTheory.ThetaIntegrand.integrableOn_form (hω i t) (D.sp.V_sig _) (hm.vpos i) (R.cV i) (hm.cV i) (R.βV i)
    (R.datVt i t) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t)) (hp i t) (R.ioP i e) (hm.νV i t) g

theorem exists_thetaMap : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP → ∃ th, ({ R with thF := th } : RealDat D A Ks).thP_thF_mem ∧ ({ R with thF := th } : RealDat D A Ks).thP_thF := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R h0 _ hm hω hv hp hio
  choose th hth using fun i t =>
    GlobalTheory.ThetaFiresOfMult.exists_isThetaMult_of_firesAt (firesAt hP R h0 hm hω hv hp hio i t)
  exact ⟨th, fun i t => (hth i t).1, fun i t => (hth i t).2⟩

end GlobalTheory.DefLift.ThetaMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isAdIso_eq_afIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (hι : GlobalTheory.TwU.IsAdIso ι) (x : AfE F E) : ι x = afIso F E x := by
  have key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P := by
    intro P
    have ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P := fun _ _ => rfl
    have evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P := fun _ _ => rfl
    have evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]; rfl
    rw [← sub_eq_zero]
    by_contra hne
    set d := ι x P - afIso F E x P with hd
    have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := F) (E := E) x {P} hv
    have hNP := hN P (Finset.mem_singleton_self P)
    have h1 : ι (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by
      show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)
      rw [hι.1, afIso_tmul_one]
    have hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P) := by
      rw [hd, e, map_add, map_add, h1, map_mul, map_mul, map_natCast, map_natCast]
      rw [ev, ev, evm, evm, evn]
      ring
    have hr1 : Valued.v (ι r P) ≤ 1 := (hι.2 r).1 hr P
    have hr2 : Valued.v (afIso F E r P) ≤ 1 := (mem_rInt_iff F E r).1 hr P
    have hsub : Valued.v (ι r P - afIso F E r P) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hr1 hr2)
    have hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E) := by
      rw [hd2, map_mul]
      exact mul_le_of_le_one_right' hsub
    exact lt_irrefl _ (hle.trans_lt hNP)
  exact Subtype.ext (funext key)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsXTupleChainOfLevelReading
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.weightedInner_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ (o : Formalism.L2.Forms.FrP (I.rec7 l Z)), o.IsON → ∀ (z z' : (I.per l u a).Wrow) (Pc Qc : (I.fm l u a).clsP → MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ℂ), (∀ c, Pc c ∈ CSpan (I.fm l u a).sg) → (∀ c, Qc c ∈ CSpan (I.fm l u a).sg) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c)) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z' c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c)) → (I.fm l u a).ipP z z' = ∑ c, ((Nat.card ((I.fm l u a).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (I.fm l u a).sg (Qc c) (Pc c) := by
  intro B X I hI hP l Z u a o ho z z' Pc Qc _ _ hz hz'
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hG : ∀ τ, gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) τ = 1 := fun τ => by
    rw [hgP, gramC_one]
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  show (I.perIn u a).ipP B.fields.emb B.embLL (l.per u a) z z' = _
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : z c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz c
  have e2 : z' c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz' c
  show (I.perIn u a).wt c * ipVal B.fields.emb B.embLL (I.perIn u a).sgT (z c) (z' c) = _
  rw [e1, e2]
  exact congrArg₂ (· * ·) rfl (MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u a).sgT hl hsh hG id (fun _ => rfl) o ho (Pc c) (Qc c))

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.norm_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (K : ClassesAtPrimes (I.fm l u a) bad) {okW : (I.rec7 l Z).what₂.places.Pl → Prop} (V : ValuationAtPrimes K okW), (∀ z, V.eW z = GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z) → NormPTieG V := by
  intro B X I hI hP l Z u a bad K okW V hV s x Pc hPc o ho
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have h := @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (I.perIn u a).sgT (I.stX a) (base_fOk B)
    (l.per u a).step (l.fmL u a).famP ((I.perIn u a).clFin (l.per u a)) _ hl _ hsh _ _
    (fun τ => by rw [hgP, gramC_one]; rfl) (fun y => (y : Formalism.L2.Forms.FrP (I.rec7 l Z))) (fun _ => rfl) s x Pc
    (fun c z => by
      have e := (congrFun (hV ((I.fm l u a).ptEmb x)) c).symm.trans (hPc c)
      exact congrFun e z) o ho
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rfl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Col2.TwP.forms_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  intro B X I hI hP l Z u a Q K hQ hQv hK
  let V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T) :=
    { sg := GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho I hI hP l Z u a
      eW := GlobalTheory.Mem.Col2.TwP.eWt I l Z u a
      ptC := GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms I hI hP l Z u a Q K hQ hQv hK
      ipP := GlobalTheory.Mem.Col2.TwP.weightedInner_twisted I hI hP l Z u a
      rat := GlobalTheory.T.tupleChain_forms_rational_iff_frame_values I hI hP l Z u a
      lat := GlobalTheory.T.tuple_integralForms_row_place_by_place I hI hP l Z u a Q K hQ hQv hK }
  refine ⟨V, GlobalTheory.Mem.Col2.TwP.norm_tw I hI hP l Z u a K V fun _ => rfl, fun z c s s' h => ?_⟩
  exact GlobalTheory.Mem.Col2.TwP.eWt_apply I l Z u a z c s s' h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.IntegralityCompare

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → ∃ R0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      MvPolynomial.map D.what₂.embLL R0 = P0 := by
  intro h
  have hle : Formalism.L2.Forms.RatSpan D lam ≤ (MvPolynomial.map D.what₂.embLL).toAddMonoidHom.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro p ⟨r, f, -, rfl⟩
    refine ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hc : (D.what₂.embLL).comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    simp [Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_rename, hc]
  obtain ⟨R0, hR0⟩ := hle h
  exact ⟨R0, hR0⟩

theorem lattice_iff_weyl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hRat Bm hBm v hv
  obtain ⟨P0, hP0, hf⟩ := hRat
  have hL : ∀ τ, GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ (((I.stp u μ i).rep c).1.1.deco.1.N) (Bs u μ w i c τ) := by
    intro τ
    have h := hBas u μ w i hi.le c τ
    have e := hStd.lat u μ i c
    exact (congrArg (fun L => GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ L (Bs u μ w i c τ)) e).mp h
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_change_integral_unit_det _ (Pl.lam w) τ _ Bm _ (hL τ) hBm
  obtain ⟨k, hk1, hk⟩ := GlobalTheory.T.chainStep_weight_arithmetic I hOk hPins l Z u μ i hi
  obtain ⟨R0, hR0⟩ := lift_ratSpan _ _ P0 hP0
  have hsrc := GlobalTheory.T.twistedSourceValue_read_in_changed_bases I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f P0 hf R0 hR0 k hk1 Bm g hg3 v hv
  set R := twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 with hRdef
  have hR : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (embT (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 := by
    have h := map_twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 (I.rec7 l Z).what₂.embLL
    have h' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 :=
      h.trans (congrArg (twSub _ Bm _) hR0)
    have he : (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) = embT (I.rec7 l Z) :=
      funext fun τ => RingHom.ext fun x => Formalism.L2.G.Cmp.tEL_emb _ τ x
    rw [he] at h'
    exact h'
  set c0 := ∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) with hc0def
  have hc0 : ‖c0‖ = 1 := by
    rw [hc0def, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2 τ, _root_.one_zpow]
  have hRat' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i) := by
    rw [hR]; exact GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan _ _ Bm _ P0 hP0
  have hν : nuT (I.rec7 l Z) u i = fun τ r => (((I.fm l u μ).lam i τ).natW r) + k τ :=
    funext fun τ => funext fun r => hk τ r
  refine (GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem (embT (I.rec7 l Z)) Bm _ _ P0 _ eY f hf).trans ?_
  rw [← hR]
  refine (GlobalTheory.T.integralSpan_iff_padic_weylDualLattice _ Pl w _ R hRat').trans ?_
  rw [hsrc, hν]
  refine Iff.trans ?_ (GlobalTheory.T.weyl_lattice_dual_invariant_unit _ _ _ _ g c0 (fun y => (∏ τ, (y τ).det ^ k τ) * polFun (MvPolynomial.map (Pl.iL w) R) y) hc0 hg1 hg2).symm
  exact (GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff _ _ _ _ k _).symm

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimePrimesNotOverBadPrimePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem vT_notOver_SBof : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  intro B X I hI a P v hP u P' hP' hv'
  have hok := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT : ((B.primes X).T u : 𝓞 B.fields.E) ∉ P.1.asIdeal :=
    GlobalTheory.MuOffMove.level_notMem_rowSG hok hI.sel_ok (hI.T_mem u) P.2
  have hpi : (B.primes X).piT u ∈ P'.asIdeal := Formalism.L2.Col.decoFin_mem_of_mem_divs hP'
  have hTP' : ((B.primes X).T u : 𝓞 B.fields.E) ∈ P'.asIdeal := by
    rw [← hok.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  rcases Formalism.L2.Col.rll_over_cases B.sp.cm hP hv' with h | h
  · subst h
    exact hT hTP'
  · subst h
    rw [Formalism.L2.Col.mem_conjP, map_natCast] at hTP'
    exact hT hTP'

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem T_notMem_qv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  classical
  intro B X I hI _ u a P
  have hP : P.1 ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union.2 (Or.inr (I.mem_SQ.2 ⟨a, P.2⟩))
  exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 hP

end GlobalTheory.Mem.Col2.ChEx
end

