import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0302
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Imports
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsJoin
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0298
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0289
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0188
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AbelianPartIntegralPointBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt
open LevelTowerAlt.LocalPrimeBound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem abelian_part_integral_point_bis : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A hpq hdisc hfree hA s
  classical
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  obtain ⟨hact, hlab, hΛ, -⟩ := hA
  obtain ⟨ML, hML⟩ := (LieMove.main L 𝔐.X (spMap (algebraMap (𝓞 L) L) ≫ z) 𝔐.t.G P.tK.G P.m.φ V P.m.cart).2 MV
  have hactL : ML.IsActOf 𝔐.t.act.act A.ρ := fun a x => Over.OverMorphism.ext (by
    rw [← hML, hact a x, Over.comp_left, Over.comp_left, Category.assoc, P.m.act, ← hML, Category.assoc])
  let jE : CMType H ⊕ CMType H → (E →+* L) := fun s => IsFractionRing.lift (A.σ_inj s)
  let σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L) := fun s => RingOfIntegers.mapRingHom (jE s)
  have hσ₀ : ∀ s, (algebraMap (𝓞 L) L).comp (σ₀ s) = A.σ s := fun s => RingHom.ext fun a =>
    IsFractionRing.lift_algebraMap (A.σ_inj s) a
  have hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)) :=
    fun s a => by
      have h := hlab s a
      rw [← hσ₀] at h
      exact h
  have hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s) := by
    simpa only [hσ₀] using A.σ_bij.1
  have hex : ∀ p : ℕ, ∃ (κ : Ω) (k : 𝓞 L), p ∈ S → (HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p κ ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap (𝓞 L) L k)) ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
    intro p
    by_cases hpS : p ∈ S
    swap
    · exact ⟨0, 0, fun h => absurd h hpS⟩
    have hp := 𝔐.S_prime p hpS
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hG.2.2.2.2.2.2.1 E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq (hfree p hpS)
    have hne : Ideal.span {(p : 𝓞 L)} ≠ ⊤ := fun h => by
      have h1 := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, RingOfIntegers.rank] at h1
      exact (Nat.one_lt_pow Module.finrank_pos.ne' hp.one_lt).ne' h1
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpQ : (p : 𝓞 L) ∈ Q := hle (Ideal.mem_span_singleton_self _)
    have h1 := (hS _ (inFibre_loc 𝔐 z Q hpQ)).1
    have hq : (⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime Q)) ≫ z), 𝔐.all _⟩ : Cpt 𝔐.ξ) =
        ⟨z (⟨Q, hQ.isPrime⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ := Subtype.ext (centre_loc z Q)
    rw [hq] at h1
    obtain ⟨r, -, -, hr, -⟩ := PtHt.FinFrame.reg_value z hξ ⟨Q, hQ.isPrime⟩ (𝔐.all _) h1
    obtain ⟨a1, a2⟩ := value_cp hξ hp hκ hr
    obtain ⟨k, rfl, b1, b2⟩ := const_int hp a1 a2
    exact ⟨κ, k, fun _ => ⟨⟨hfree p hpS, hS, hr⟩, b1, b2⟩⟩
  choose κ k hk using hex
  obtain ⟨n1, n2⟩ := norm_bound (jE s) S k fun p hp => (hk p hp).2
  have hset : ∀ 𝔭 : PrimeSpectrum (𝓞 L), {x' : V | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
      ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left} =
      {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun 𝔭 => by
    ext x'
    constructor
    · rintro ⟨e, he, v, hv, h⟩
      have e' : v = ML.pt x' := Over.OverMorphism.ext (h.symm.trans (hML _))
      exact ⟨e, he, e' ▸ hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, _, hv, hML _⟩
  have hF : ∀ x, x ∈ 𝔐.FibLat (𝔐.V s) z P MV ↔ ∀ 𝔭 : PrimeSpectrum (𝓞 L), ∃ t ∉ 𝔭.asIdeal, t • x ∈
      Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun x => by
    simp only [HodgeCpt.FibLat, hset, Submodule.mem_iInf]
    exact forall_congr' fun 𝔭 => PtHt.FinFrame.span_sat_iff 𝔭.asIdeal le_rfl
      (fun u hu => ⟨1, (Ideal.ne_top_iff_one _).1 𝔭.isPrime.ne_top, by rwa [one_smul]⟩) x
  have hcc : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime], ∃ cc : Localization.AtPrime Q →+* L,
      cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L := fun Q _ => by
    have hunit : ∀ d : Q.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d =>
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
        fun e => d.2 (e ▸ Q.zero_mem))
    exact ⟨IsLocalization.lift (M := Q.primeCompl) hunit, IsLocalization.lift_comp hunit⟩
  have hloc := fun (Q : Ideal (𝓞 L)) [Q.IsPrime] cc hc =>
    loc 𝔐 z ML A.ρ hactL σ₀ hσ hinj κ k (fun p hp => (hk p hp).1) hdisc s Q cc hc
  rw [hσ₀] at hloc
  refine ⟨_, n1, Submodule.smul_le.2 fun a ha x hx => ?_, Submodule.smul_le.2 fun a _ x hx => ?_, n2⟩
  · have hx' := (hF x).1 hx
    have key : ∀ d ∈ differentIdeal ℤ (𝓞 E), (∏ p ∈ S, k p) • σ₀ s d • x ∈ A.eig s := fun d hd => by
      refine ⟨(hΛ _).2 ?_, ?_⟩
      · let MB := LiePull.extModel (g := algebraMap (𝓞 L) L) (x := z) (FaithfulSMul.algebraMap_injective _ _) rfl ML
        obtain ⟨e, he⟩ := GlobalTheory.T.tangent_vector_extends_dvr (𝓞 L) L 𝔐.X z 𝔐.t.G _ MB (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)) (ML.tan _)
          fun Q hQ cc hc => ((hloc Q cc hc).2 x (hx' ⟨Q, hQ.isPrime⟩) d hd).2
        exact ⟨MB.pt e, MB.tan e, (hML _).trans ((Category.comp_id _).symm.trans he)⟩
      · obtain ⟨cc, hc⟩ := hcc ⊥
        exact ((hloc ⊥ cc hc).2 x (hx' ⟨⊥, Ideal.isPrime_bot⟩) d hd).1
    have h1 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V ((∏ p ∈ S, k p) • x)) :=
      Ideal.map_le_iff_le_comap.2 fun d hd => by
        show σ₀ s d • (∏ p ∈ S, k p) • x ∈ A.eig s
        rw [smul_comm]
        exact key d hd
    have h2 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) * Ideal.span {∏ p ∈ S, k p} ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V x) :=
      Ideal.mul_le.2 fun r hr t ht => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
        show (r * (u * ∏ p ∈ S, k p)) • x ∈ A.eig s
        rw [mul_left_comm, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (h1 hr)
    exact h2 ha
  · refine Submodule.smul_mem _ _ ((hF x).2 fun 𝔭 => ?_)
    obtain ⟨cc, hc⟩ := hcc 𝔭.asIdeal
    obtain ⟨v, hv, hxv⟩ := (hΛ x).1 hx.1
    exact (hloc 𝔭.asIdeal cc hc).1 x hx.2 ⟨v, hv, (hML x).symm.trans hxv⟩

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentHeightLowerBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt

theorem ph_usc {n : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas n X}
    (B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A) (x : X) (r : ℝ) (hr : B.ph x < r) :
    ∀ᶠ x' in 𝓝 x, B.ph x' < r := by
  obtain ⟨j, hj⟩ := B.cover x
  have hs : x ∈ (B.chart j).source :=
    B.toPotentialCharts.mid_subset_source j (B.toPotentialCharts.inner_subset_mid j hj)
  have ht := (B.chart j).map_source hs
  have hn : (B.chart j).target ∈ 𝓝 (B.chart j x) := (B.chart j).open_target.mem_nhds ht
  have h1 : ∀ᶠ y in 𝓝[(B.chart j).target] (B.chart j x),
      B.q j y + B.ph ((B.chart j).symm y) < B.q j (B.chart j x) + B.ph x + (r - B.ph x) / 2 :=
    (B.u_psh j).1 _ ht _ (by
      show B.q j (B.chart j x) + B.ph ((B.chart j).symm (B.chart j x)) < _
      rw [(B.chart j).left_inv hs]; linarith)
  rw [nhdsWithin_eq_nhds.2 hn] at h1
  have h2 : ∀ᶠ y in 𝓝 (B.chart j x), B.q j (B.chart j x) - (r - B.ph x) / 2 < B.q j y :=
    ((B.q_smooth j).continuousOn.continuousAt hn).eventually (lt_mem_nhds (by linarith))
  have hc := (B.chart j).continuousAt hs
  filter_upwards [hc.eventually h1, hc.eventually h2, (B.chart j).open_source.mem_nhds hs] with y a b c
  rw [(B.chart j).left_inv c] at a
  linarith

theorem Xo_dense {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type}
    [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (D : ComponentData II Ψ K J Ω W) {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal D.y)) :
    (𝓝[D.Xo] w).NeBot := by
  classical
  obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover w hw
  have ht1 : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (by linarith)
  let e : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ := fun i => if t i = 0 then 1 else 0
  have h0 : Tendsto (fun s : ℝ => t + (s : ℂ) • e) (𝓝[>] 0) (𝓝 t) := by
    have : Continuous fun s : ℝ => t + (s : ℂ) • e := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hγ := ((D.chart a).analytic t ht1).continuousAt
  have hT : Continuous fun z : (Σ k, J k) → ℂ => torusSmul c z := by
    unfold torusSmul; fun_prop
  have h1 : Tendsto (fun s : ℝ => torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) (𝓝[>] 0)
      (𝓝[D.Xo] (torusSmul c ((D.chart a).γ t))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(hT.tendsto _).comp (hγ.tendsto.comp h0), ?_⟩
    filter_upwards [h0.eventually (Metric.isOpen_ball.mem_nhds ht1), self_mem_nhdsWithin] with s hs hs0
    have hm := (D.chart a).mem _ hs
    refine ⟨mcPts_smul D.arith.2.1.2.1 c hc hm, fun hb => ?_⟩
    have hb' := D.bd_torus _ hb (fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
    have he : torusSmul (fun k => (c k)⁻¹) (torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) =
        (D.chart a).γ (t + (s : ℂ) • e) := by
      funext p
      simp [torusSmul, hc]
    rw [he, (D.chart a).boundary _ hs] at hb'
    obtain ⟨i, -, hi⟩ := hb'
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hs0)
    by_cases h : t i = 0 <;> simp [e, h, hs'] at hi
  exact h1.neBot

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.HodgeCompactCoverPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_root (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (hpos : 0 < D.p + D.q)
    (p : ℕ) (hp : p ∈ S) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p) := by
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
  let q : Cpt A.ξ := ⟨_, specializes_rfl⟩
  exact (GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) q A.tie.gen
    (pow_pos (A.S_prime p hp).pos _) (A.tors p hp) (A.normal q.1).2
    (HcptPull.noeth_stalk A.tie.gen q ((GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1 q))).2.1 hpos

theorem exists_flagged (hW : Out.WeilSt) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (dg : ℕ)
    (hcov : A.IsCover dg) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hHT : ∀ p ∈ S, HT.HTFree A p) :
    ∃ (Ω' : Type) (_ : Field Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k))
      (y' : (Σ k, J' k) → Ω') (B : HodgeCpt Y S y') (Fl : B.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Ω') (i : Ω →+* Ω') (g : B.X ⟶ A.X) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)),
      Nonempty K' ∧ Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧
      GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ g i ∧ B.f = g ≫ A.f ∧ B.R = A.R ∧ (∀ p ∈ S, HT.HTFree B p) ∧
      Fl.RootLines xdeg e := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · have hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A.ξ (𝟙 _) (RingHom.id Ω) := by
      unfold GlobalTheory.CompanionTheory.Ar.Dominates
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, hne, hinj, hy, hT⟩ := exists_join A.tie A.tie (𝟙 _) (RingHom.id Ω) hd
    obtain ⟨Fl⟩ := flag_zero (reTie A hT) dg hcov h0
    haveI : IsEmpty (CMType H × Fin (D.p + D.q)) := ⟨fun r => by have := r.2.2; omega⟩
    exact ⟨Ω, _, K₃, _, J₃, inferInstance, y₃, reTie A hT, Fl, fun _ => 0, fun _ => 1, RingHom.id Ω, 𝟙 _, bk, bx, hne, hinj, hy, hd,
      (Category.id_comp _).symm, rfl, hHT, isEmptyElim⟩
  · have hζ := exists_root A x hx hpos
    obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
      GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K J y A x dg hx hS hHT hζ hcov
    have hBy : B.ξ ≫ B.f = (spMap i ≫ x) ≫ Y.j := by
      rw [hBf, ← Category.assoc, hg₂, Category.assoc, hx, Category.assoc]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, ⟨k₀⟩, hinj, hy, hT⟩ := exists_join A.tie B.tie g₂ i hg₂
    obtain ⟨K₄, _, J₄, _, y₄, bk', bx', C, g₃, Fl, xdeg, e, hinj', hy', hg₃, hCf, hCR, -, hC, -, -, hroot, -⟩ :=
      GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₃ J₃ y₃ (reTie B hT) (spMap i ≫ x) b Li₀ a₀ m₀ M₀ j V₀ dg hBy hS hB
        (fun p hp => by
          obtain ⟨ζ, hζ'⟩ := hζ p hp
          exact ⟨i ζ, by rw [show (reTie B hT).R = A.R from hBR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
    refine ⟨Ω', _, K₄, _, J₄, inferInstance, y₄, C, Fl, xdeg, e, i, g₃ ≫ g₂, bk' ∘ bk, fun k => (bx k).trans (bx' (bk k)),
      ⟨bk' k₀⟩, hinj'.comp hinj, fun k a => (hy' _ _).trans (hy k a), ?_, ?_, hCR.trans hBR, hC, hroot⟩
    · have h3 : C.ξ ≫ g₃ = B.ξ := by
        have h := hg₃
        unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
        rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show C.ξ ≫ g₃ ≫ g₂ = _
      rw [← Category.assoc, h3]
      exact hg₂
    · rw [Category.assoc, ← hBf]; exact hCf

end

theorem hodge_compact_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  intro hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y A dg inst hcov hS hHT
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y S Ω K J y A hβ
  obtain ⟨Ω', _, K', _, J', _, y', B, Fl, xdeg, e, i, g, bk, bx, hne, hinj, hy, hd, hf, hR, hB, hroot⟩ :=
    exists_flagged hW A x hx dg hcov hS hHT
  obtain ⟨j, hext, hV⟩ := exists_pull A B g i x hx hS (fun p hp => (hHT p hp).2) hd hf hR
  obtain ⟨hbir, har⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c _ _ Y S Ω' K' J' y' B Fl hβ
  have har' : IsArithVar (mCoordIdeal y') (@Fintype.card (CMType H) inst * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
    convert har
  choose L hL using GlobalTheory.T.exists_smooth_conj_invariant_metric K' J'
  exact ⟨{ K := K', «ι» := J', Ω := Ω', y := y', arith := har', birational := hbir, xdeg := xdeg,
           x := fun _ r => L (xdeg r), x_deg := fun _ _ => (hL _).1, x_smooth := fun _ _ => (hL _).2.1,
           x_conj := fun _ _ => (hL _).2.2, kA := 1, kA_pos := one_pos, A := L 0, A_smooth := (hL _).2.1,
           A_conj := (hL _).2.2, δ := 1, δ_pos := one_pos },
    B, Fl, e, i, g, bk, bx, j, hinj, hy, hd, hB, hroot, hext.1, hext.2, hV⟩

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LvExtCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OmLink

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem lv_ext_cancel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} {k : Type} [Field k]
    (i : Ω →+* k) {x x' : Over.mk ξ ⟶ G} (h : GenWeilModel.ext i ≫ x = GenWeilModel.ext i ≫ x') : x = x' := by
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun f => Over.Hom.left f) h
  simp only [Over.comp_left, GenWeilModel.ext, Over.homMk_left] at h1
  have := epi_sp i
  exact (cancel_epi _).1 h1

section obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

theorem lv_push_pow {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S'} (a : T ⟶ G') (n : ℕ) :
    pushPt hp.1.w (a ^ n) = pushPt hp.1.w a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact push_one hp T
  | succ n ih => rw [pow_succ, pow_succ, push_mul hp, ih]

theorem lv_div (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) (y : Over.mk ξ ⟶ t.G) (hy : y ^ n = 1) :
    ∃ x : Over.mk ξ ⟶ t.G, x ^ (n * r) = 1 ∧ x ^ r = y := by
  classical
  have hp := m.cart
  let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨a, ha, hpa⟩ := pull_point hp i y hy
  obtain ⟨T⟩ := exists_tate o i
  obtain ⟨α, rfl⟩ := (T.onto n hn a).1 ha
  have hnr : 0 < n * r := Nat.mul_pos hn hr
  obtain ⟨y', -, hy'a⟩ := desc hp hf i (T.ev (n * r) α) ((T.onto (n * r) hnr _).2 ⟨α, rfl⟩)
  let x : Over.mk ξ ⟶ t.G := Over.homMk (y'.left ≫ m.cm.F) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w y']
    simp)
  have hx : GenWeilModel.ext i ≫ x = pushPt hp.1.w (T.ev (n * r) α) := by
    apply Over.OverMorphism.ext
    rw [hy'a]
    simp [x, pushPt, GenWeilModel.ext, ex]
  have hcp : ∀ j : ℕ, GenWeilModel.ext i ≫ x ^ j = (GenWeilModel.ext i ≫ x) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  refine ⟨x, lv_ext_cancel i ?_, lv_ext_cancel i ?_⟩
  · rw [hcp, hx, ← lv_push_pow hp, (T.onto (n * r) hnr _).2 ⟨α, rfl⟩, push_one hp, MonObj.comp_one]
  · rw [hcp, hx, ← lv_push_pow hp, T.tower n r hn hr α, hpa]

theorem lv_down [CharZero Ω] (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hf : FullTorsion t.G ξ (n * r)) {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (x : Over.mk ξ ⟶ t.G) (hx : x ^ (n * r) = 1) (q : Cpt ξ) (w : Module.Dual Ω V)
    (h : M.IsHTAt t.PP.L (n * r) x q w) : M.IsHTAt t.PP.L n (x ^ r) q w := by
  obtain ⟨h0, W, f, h1, h2, h3⟩ := h
  refine ⟨h0, W, f, h1, fun k _ _ i xk g c hW hxk hg hc => ?_, fun e v hev hv => ?_⟩
  · have hp := m.cart
    have hg' : g ^ (n * r) = 1 := by rw [pow_mul, hg, one_pow]
    obtain ⟨g₀, hg₀⟩ := hf k i g hg'
    have hg₁ : g = GenWeilModel.ext i ≫ g₀ := Over.OverMorphism.ext hg₀
    have hg₂ : g₀ ^ n = 1 := lv_ext_cancel i (by rw [MonObj.comp_pow, ← hg₁, hg, MonObj.comp_one])
    obtain ⟨a, ha, hpa⟩ := pull_point hp i x hx
    obtain ⟨a', ha', hpa'⟩ := pull_point hp i g₀ hg₂
    have e1 : a'.left ≫ m.φ = g.left := (congrArg (fun z => z.left) hpa').trans hg₀.symm
    have e2 : a.left ≫ m.φ = (GenWeilModel.ext i ≫ x).left := congrArg (fun z => z.left) hpa
    have e3 : (a ^ r).left ≫ m.φ = xk.left := by
      have h4 := lv_push_pow hp a r
      have h5 : pushPt hp.1.w (a ^ r) = GenWeilModel.ext i ≫ x ^ r := by
        rw [MonObj.comp_pow]
        exact h4.trans (congrArg (· ^ r) hpa)
      exact (congrArg (fun z => z.left) h5).trans hxk.symm
    refine h2 k i (GenWeilModel.ext i ≫ x) g c hW rfl hg' ?_
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) a a' _ g (n * r) c e2 e1]
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) (a ^ r) a' xk g n c e3 e1] at hc
    have hk : CharZero k := charZero_of_injective_ringHom i.injective
    have hu : IsUnit ((n * r : ℕ) : Γ((Over.mk (spMap i)).left, ⊤)) := by
      have h6 : IsUnit ((n * r : ℕ) : k) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hr).ne').isUnit
      have h7 := h6.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      rwa [map_natCast] at h7
    have h8 := ((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))).2.2.2 r a a' (unitOn c) hu ha ha').2 hc
    rw [Nat.cast_mul]
    exact h8
  · obtain ⟨u, hu, he⟩ := h3 e v hev hv
    refine ⟨r * u, mul_mem (natCast_mem _ r) hu, ?_⟩
    rw [he]
    push_cast
    ring

end obj

theorem lv_kappa {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    (hq : IsIntegrallyClosed (X.presheaf.stalk q.1)) {p : ℕ} (hp : p.Prime) {κ : Ω} (h : HT.IsCp p κ) :
    ∃ a ∈ regAt ξ q, ((p ^ 4 : ℕ) : Ω) = a * κ := by
  classical
  unfold HT.IsCp at h
  split_ifs at h with h2
  · subst h2 h
    refine ⟨4, ?_, by norm_num⟩
    simp
  · obtain ⟨ζ, hζ, rfl⟩ := h
    have hfact : Fact p.Prime := ⟨hp⟩
    have hmem : ζ ∈ primitiveRoots p Ω := (mem_primitiveRoots hp.pos).2 hζ
    have hc := congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at hc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hc
    rw [← Finset.mul_prod_erase _ _ hmem] at hc
    refine ⟨-((p : Ω) ^ 3) * ∏ z ∈ (primitiveRoots p Ω).erase ζ, (1 - z), ?_, ?_⟩
    · apply GlobalTheory.T.integral_element_regular X Ω ξ q hξ hq
      refine IsIntegral.mul (IsIntegral.neg (IsIntegral.pow (isIntegral_natCast p) 3)) ?_
      refine IsIntegral.prod _ fun z hz => IsIntegral.sub isIntegral_one ?_
      exact ((mem_primitiveRoots hp.pos).1 (Finset.mem_of_mem_erase hz)).isIntegral hp.pos
    · push_cast
      rw [pow_succ, hc]
      ring

theorem levelFree : LevelFree := by
  intro hF E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 p hpS hpq hfree q hq
  have hp := 𝔐.S_prime p hpS
  haveI := Fact.mk hp
  have : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y 𝔐 hmono
  have hx₀ : 𝔐.ξ ≫ 𝔐.f = (spMap 𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']
    exact 𝔐.fn_over
  obtain ⟨s0, o, ⟨m⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y 𝔐.X 𝔐.f 𝔐.t 𝔐.m Ω 𝔐.ξ _ hx₀
  have hno := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have hnc := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq hfree
  have hR : p ^ 𝔐.R p = p ^ 4 * p ^ (𝔐.R p - 4) := by
    rw [← pow_add, Nat.add_sub_cancel' (𝔐.R_ge p hpS)]
  have hsw := (hS q hq).2.2.1
  have hf := 𝔐.tors p hpS
  unfold HT.omP at hsw
  rw [hR] at hsw hf ⊢
  obtain ⟨a, ha, hae⟩ := lv_kappa 𝔐.tie.gen q (𝔐.normal _).2 hp hκ
  have hn : 0 < p ^ 4 := pow_pos hp.pos _
  have hr : 0 < p ^ (𝔐.R p - 4) := pow_pos hp.pos _
  generalize p ^ (𝔐.R p - 4) = r at *
  generalize p ^ 4 = n at *
  have hf' : FullTorsion 𝔐.t.G 𝔐.ξ n := fun k _ i g hg => hf k i g (by rw [pow_mul, hg, one_pow])
  have hw : ∀ N, 0 < N → FullTorsion 𝔐.t.G 𝔐.ξ N → ∃ e, GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ N e := fun N hN hfN => by
    have := GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l _ _ (Sp Ω) _ s0 o 𝔐.t 𝔐.ξ m Ω (𝟙 _) N hN
      (by rwa [Category.id_comp]) (root o 𝔐.t m hfN hN hpq)
    rwa [Category.id_comp] at this
  obtain ⟨e, he⟩ := hw n hn hf'
  obtain ⟨e', he'⟩ := hw _ (Nat.mul_pos hn hr) hf
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro w ⟨z, hz, hw⟩
    obtain ⟨x, hx, rfl⟩ := lv_div o 𝔐.t m hn hr hf z hz
    obtain ⟨U, hU, w', hw'⟩ := (GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ (Nat.mul_pos hn hr) hf e' he'
      _ 𝔐.M q).1
    have h1 := hw' x hx q hU
    obtain ⟨u, hu, rfl⟩ := ((GlobalTheory.T.hodge_tate_weil_local _ Ω 𝔐.ξ 𝔐.tie.gen hnc 𝔐.t.G 𝔐.t.semi 𝔐.t.PP.L _ hn hf' e he _ 𝔐.M q).2 _ _ w hz
      (lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q _ h1)).1 hw
    refine add_mem (Submodule.subset_span ⟨x, hx, h1⟩) ?_
    have h2 : n • u = (⟨a, ha⟩ : regAt 𝔐.ξ q) • κ • u := by
      rw [← Nat.cast_smul_eq_nsmul Ω, hae, mul_smul]
      rfl
    exact h2 ▸ Submodule.smul_mem _ _ (hsw u hu)
  · rintro w ⟨x, hx, hw⟩
    exact Submodule.subset_span ⟨x ^ r, by rw [← pow_mul, Nat.mul_comm, hx], lv_down o 𝔐.t m hn hr hf 𝔐.M x hx q w hw⟩

end LevelTowerAlt.Comparison₂
end
end

