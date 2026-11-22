import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquare
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Formalism.PeriodIntegrals.Bundle0018
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesCompatibleEventuallyOfGerm
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEventually

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

section Jets

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem mk_eq_zero_iff (p : MvPolynomial ι R) :
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, show orig R ι = MvPolynomial.idealOfVars ι R from rfl,
    MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE [Fintype ι] [DecidableEq ι] (e : ι →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]

theorem coeff_eq_of_psJet_eq [Fintype ι] [DecidableEq ι] {f g : MvPowerSeries ι R} (h : psJet m f = psJet m g)
    (e : ι →₀ ℕ) (he : e.degree ≤ m) : MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by
  rw [← sub_eq_zero, psJet, psJet, ← map_sub, mk_eq_zero_iff] at h
  have := h e he
  rwa [coeff_sub, coeff_psTrunc, coeff_psTrunc, if_pos he, if_pos he, sub_eq_zero] at this

theorem psJet_prod [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α] (S : Finset α) (g : α → MvPowerSeries ι R) :
    psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]

theorem psJet_pow [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

variable {K : Type} [CommRing K] (f : R →+* K)

theorem jetCoef_injective (hf : Function.Injective f) : Function.Injective (jetCoef f ι m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [JetTr.jetCoef_mk, mk_eq_zero_iff] at ha
  rw [mk_eq_zero_iff]
  intro e he
  apply hf
  rw [map_zero, ← ha e he, coeff_map]

theorem map_psIn {d n n' : ℕ} (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) R) :
    MvPolynomial.map f (psIn d m r g) = psIn d m r (MvPowerSeries.map f g) := by
  rw [psIn, psIn, map_rename, JetTr.psTrunc_map]

theorem jetCoef_subst2 {d : ℕ} {κ : Type} (u v : Fin d → MvPolynomial κ R) (u' v' : Fin d → MvPolynomial κ K)
    (hu : ∀ j, MvPolynomial.map f (u j) = u' j) (hv : ∀ j, MvPolynomial.map f (v j) = v' j)
    (a : Jet R (Fin 2 × Fin d) m) :
    jetCoef f κ m (jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) a) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2)
        (jetCoef f (Fin 2 × Fin d) m a) := by
  have e : (fun p : Fin 2 × Fin d => (![u', v'] : Fin 2 → Fin d → MvPolynomial κ K) p.1 p.2) =
      fun p : Fin 2 × Fin d => MvPolynomial.map f ((![u, v] : Fin 2 → Fin d → MvPolynomial κ R) p.1 p.2) := by
    funext ⟨i, j⟩
    fin_cases i
    · exact (hu j).symm
    · exact (hv j).symm
  rw [e]
  exact RingHom.congr_fun (JetTr.jetCoef_substP f m _) a

end Jets

section Rat

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem jetCopy_psJet {n : ℕ} (m : ℕ) (i : Fin n) (g : PS S 1 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (psJet m g) =
      psJet m (ev (n := n) ![pt S d i] g) := by
  rw [← jetSubstP_psJet m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) ![pt S d i]
    (fun ⟨a, j⟩ => by fin_cases a; exact cc_pt' i j) (fun p => by simp)
    (fun ⟨a, j⟩ => by fin_cases a; exact mk_X_psJet m (i, j))]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  simp only [jetCopy, jetSubstP, GermD.jetMap_mk, aeval_X, constantCoeff_X, map_zero, sub_zero]

theorem jetCopy_graph {n : ℕ} (m : ℕ) (i : Fin n) (w : Pt S 1 d) (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0)
    (g : PS S 2 d) :
    (jetCopy (S := S) d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m)
      (jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (w j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) (psJet m g)) =
      psJet m (ev (n := n) ![pt S d i, comp1 w (pt S d i)] g) := by
  have hr : (![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) = fun i => pt S d ((![0] : Fin 1 → Fin 1) i) := by
    funext i; fin_cases i; rfl
  have ha : ∀ a j, MvPowerSeries.constantCoeff
      ((![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) a j) = 0 := by
    intro a j; fin_cases a
    · exact cc_pt' _ j
    · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_comp1 _ _ hw (fun i => cc_pt' _ i) j
  have hb : ∀ a j, MvPowerSeries.constantCoeff ((![pt S d i] : Fin 1 → Pt S n d) a j) = 0 := by
    intro a j; fin_cases a; exact cc_pt' _ j
  rw [jetSubstP_psJet m _ (![pt S d 0, comp1 w (pt S d 0)] : Fin 2 → Pt S 1 d) (fun p => ha p.1 p.2)
      (fun ⟨a, j⟩ => by
        fin_cases a
        · simp
        · show constantCoeff (psIn d m ![0] (w j)) = 0
          rw [FBIdPh.cc_psIn, hw])
      (fun ⟨a, j⟩ => by
        fin_cases a
        · exact mk_X_psJet m _
        · show _ = psJet m (ev ![pt S (n := 1) d 0] (w j))
          rw [hr]
          exact mk_psIn_psJet m _ _),
    jetCopy_psJet, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_ev _ _ ha hb]
  congr 2
  funext a j
  fin_cases a
  · exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.ev_X _ hb 0 j
  · exact ev_at _ hb 0 (w j)

end Rat

theorem unit_eq_one {V F : Type} [CommRing V] [Field F] [CharZero F] [Algebra V F]
    (hf : Function.Injective (algebraMap V F)) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (bar : O → O) (w0 : O) (hw : w0 + bar w0 = 1) {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (h : PS F n d) (k : ℕ)
    (hk : ∀ (m : ℕ) (u : PS F n d), (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e (h * u) = 0) →
      ∀ e : Fin n × Fin d →₀ ℕ, e.degree + k ≤ m → MvPowerSeries.coeff e u = 0)
    (m : ℕ) (hm : k + 2 ≤ m) (U : (Jet V (Fin 2 × Fin d) m)ˣ)
    (h1 : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (B.G.F j),
        fun j => X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2)
        (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hs : jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) = U)
    (hb : ∀ a, jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m) =
      jetSubstP m (fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act (bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))
    (hrel : psJet m h * ∏ i : Fin n,
      (jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m)
        (jetCoef (algebraMap V F) (Fin 1 × Fin d) m (jetSubstP m (fun p : Fin 2 × Fin d =>
          (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (B.A.act w0 j)] :
            Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2) (U : Jet V (Fin 2 × Fin d) m))) ^ q =
      psJet m h) : U = 1 := by
  set f := algebraMap V F with hfd
  let BF : FB F d O := FBMap.mapFB f B
  let UF : (Jet F (Fin 2 × Fin d) m)ˣ := Units.map (jetCoef f (Fin 2 × Fin d) m).toMonoidHom U
  have hUF : (UF : Jet F (Fin 2 × Fin d) m) = jetCoef f (Fin 2 × Fin d) m U := rfl
  have hX : ∀ {r : ℕ} (i : Fin r) (j : Fin d),
      MvPolynomial.map f (X (i, j) : MvPolynomial (Fin r × Fin d) V) = X (i, j) := fun i j => map_X _ _
  obtain ⟨c, hcs, hcb, hc⟩ := CIndFrExp3.fixExp BF.G BF.A.act BF.A.const bar m UF
    (by
      have e := congrArg (jetCoef f (Fin 3 × Fin d) m) h1
      rw [map_mul, jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 2),
        jetCoef_subst2 f _ _ _ _ (hX 0) (hX 2), jetCoef_subst2 f _ _ _ _ (hX 1) (hX 2)] at e
      exact e)
    (by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) hs
      rw [jetCoef_subst2 f _ _ _ _ (hX 1) (hX 0)] at e
      exact e)
    (fun a => by
      have e := congrArg (jetCoef f (Fin 2 × Fin d) m) (hb a)
      rw [jetCoef_subst2 f _ _ _ _ (fun j => map_psIn f _ _) (hX 1),
        jetCoef_subst2 f _ _ _ _ (hX 0) (fun j => map_psIn f _ _)] at e
      exact e)
  have hc0 : c = 0 := by
    refine GlobalTheory.DiagExpZero.form_eq_zero_of_diag_exp F d BF.G (BF.A.act w0) (BF.A.act (bar w0)) (BF.A.const w0) ?_ c hcs (hcb w0) n q hn hq ?_
    · have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add F B w0 (bar w0)
      rw [hw, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one] at e
      exact e.symm
    · intro e he
      refine hk m _ (fun e' he' => ?_) e (by omega)
      rw [jetCoef_subst2 f _ _ (fun j => X ((0 : Fin 1), j)) (fun j => psIn d m ![0] (BF.A.act w0 j)) (hX 0)
        (fun j => map_psIn f _ _), ← hUF, hc] at hrel
      simp only [jetCopy_graph m _ _ (BF.A.const w0)] at hrel
      simp only [← psJet_pow] at hrel
      rw [← psJet_prod, ← FBIdJet.psJet_mul] at hrel
      rw [mul_sub, mul_one, map_sub, coeff_eq_of_psJet_eq hrel e' he', sub_self]
  rw [hc0, CIndFrFix2c.twist_zero, FBIdJet.psJet_one, hUF] at hc
  exact Units.ext (jetCoef_injective f hf (by rw [hc, Units.val_one, map_one]))

end GlobalTheory.FrameEventually

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GCorCut Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem frames_compatible_eventually_of_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf pD pA pG U' P.U) (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), 1 ≤ n → 1 ≤ q → h ≠ 0 → IsGermN P C.xT C.actT C.eT C.wPT pG PU F q σ' h → ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → LB.Gen.Corr C.I.G.PP.L _ _ _ _ (LB.pullGen C.I.G.PP.L (cφG C.I.G ![jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT (m + 1) (0 : Fin 2), jptG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT (m + 1) (1 : Fin 2)]) (cε 2) (C.eT (m + 1)) (homAt (𝟙 (Sp T.V)) (jetTrunc : Jet T.V (Fin 2 × Fin (chD C.ch)) (m + 1) →ₐ[T.V] Jet T.V (Fin 2 × Fin (chD C.ch)) m)).left) (C.eT m) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P n D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ q σ' h hn hq hh hg
  obtain ⟨k, hk⟩ := GlobalTheory.mvPowerSeries_coeff_eq_zero_of_mul_coeff_eq_zero F (Fin n × Fin (chD C.ch)) h hh
  obtain ⟨B, eF, eA, -⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  refine ⟨k + 2, fun m hm => ?_⟩
  obtain ⟨U, hU, h1, hs, hb⟩ := FrRatio.frRatioG C.chartT C.frameT m
  have hrel := GlobalTheory.GermRatio.main E H T.V (maximalIdeal T.V) C.I.G P (chD C.ch) n C.xT C.FT C.actT C.tgT _ C.chartT
    C.wPT C.primT D' A' G' pD pA pG U' PU F q σ' h C.eT C.frameT.gen hg m U hU
  have hinj : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V T.Fr F]
    exact (algebraMap T.Fr F).injective.comp (IsFractionRing.injective T.V T.Fr)
  rw [← eF] at h1
  rw [← eA] at hb hrel
  have hone : U = 1 := FrameEventually.unit_eq_one hinj B H.bar H.w0 (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) hn hq h k
    hk m hm U h1 hs hb hrel
  subst hone
  refine corr_of_val C.I.G.PP.isLB fun z J hJ => ?_
  refine (val_corr hJ hU (𝟙 _)).trans ((GermB.val_scale _ _ _ _ _ _ z J hJ).trans ?_)
  rw [unitΓ, map_one, map_one, _root_.one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGermStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvExp_linearPart_integralChar_mem_integralGerm : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (χ : MvPowerSeries κ C), IntS V χ → MvPowerSeries.constantCoeff χ = 1 → MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) χ = MvPowerSeries.subst (gp C κ (0 : Fin 2)) χ * MvPowerSeries.subst (gp C κ (1 : Fin 2)) χ → ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → upG g (mvExp (∑ x : I g, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) χ * X.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t := by
  first | exact @GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm | exact GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm | (intros; apply GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximalStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  first | exact @GlobalTheory.SeriesFrobRoot.main | exact GlobalTheory.SeriesFrobRoot.main | (intros; apply GlobalTheory.SeriesFrobRoot.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquareStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonDegenerate_formalBiextension_square : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → NonDeg (Y.rawSelf p) V := by
  first | exact @GlobalTheory.NonDegSquare.nonDeg_rawSelf | exact GlobalTheory.NonDegSquare.nonDeg_rawSelf | (intros; apply GlobalTheory.NonDegSquare.nonDeg_rawSelf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  first | exact @GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | exact GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | (intros; apply GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqFStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceLabel_bijective_card_eq_f : ∀ (D : D7), Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  first | exact @GlobalTheory.RunDepth.plOf_bijective_card | exact GlobalTheory.RunDepth.plOf_bijective_card | (intros; apply GlobalTheory.RunDepth.plOf_bijective_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConjStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  exact @GlobalTheory.InertLabelling.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RestDegAdd
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem restDeg_add {d : ℕ} [NeZero d] (bgr : ZMod d → Fin 2) (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.restDeg bgr n ga K + ∑ s, n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ s : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g s k := by
  unfold RF.restDeg
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0 := by
    rw [Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) (W : P.Pl → ℕ) :
    ∑ z ∈ Z, ∑ s : ZMod P.d, W (P.pos z s.val) = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem wtHyp_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m → (∀ z, InPsi H (pl z)) → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → ∀ (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)) (bgr : ZMod d → Fin 2) (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ)), RF.IsReps (parAt N j d pos) Z → Function.Bijective (fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2) → (∀ z s, tau z (bgr s) s = pl (pos z s.val)) → RF.WtHyp N.R.k N.R.r Z bgr (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) (fun z => RF.alongOrb (parAt N j d pos) z (gapW N pl a)) (fun _ _ => 0) (restOf N Dw pl a) := by
  intro E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
    unfold Datum.mult; split_ifs <;> omega
  have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
  have hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) =
      gapW N pl a (pos z s.val) := by
    intro z s
    rw [htau]
    have hm : Dw.mult (pl (pos z s.val)) = Dw.p := if_pos (hpsi _)
    rw [hm]
    unfold gap gapW
    rw [if_pos (by omega), if_pos (by omega)]
    rfl
  refine ⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩
  have hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i) := by
    unfold DF
    rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
  have key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) +
      (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a := by
    have hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z :=
      sum_reps (parAt N j d pos) Z hZ (gapW N pl a)
    rw [hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have := restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))
    simp only [hmain] at this
    rw [Finset.mul_sum, this]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2
  unfold restOf
  rw [← key]
  push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
  simp

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasisStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separatedEmbeddings_directions_typedBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (A : Type) [Fintype A] (tau : A → (E →+* ℂ)), (∀ s s', s ≠ s' → ∃ x : 𝓞 E, V.v (emA3 io ι (tau s) x - emA3 io ι (tau s') x) = 0) → (∀ s (x : Fin (Dw.mult (tau s))) i, V.Ge 0 (ι (chartUnitVectors C3 ⟨tau s, x⟩ i))) ∧ (∀ s (x : Fin (Dw.mult (tau s))) (a : 𝓞 E), linAct (Y.B.A.act a) (fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) = emA3 io ι (tau s) a • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) ∧ (∃ w : Fin (chD C3.ch) → (Σ s : A, Fin (Dw.mult (tau s))) → C, (∀ i q, V.Ge 0 (w i q)) ∧ ∀ q q' : (Σ s : A, Fin (Dw.mult (tau s))), ∑ i, ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i) * w i q' = if q = q' then 1 else 0) ∧ ∀ s (v : Fin (chD C3.ch) → C), (∀ a : 𝓞 E, linAct (Y.B.A.act a) v = emA3 io ι (tau s) a • v) → ∃ b : Fin (Dw.mult (tau s)) → C, v = ∑ x, b x • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i) := by
  first | exact @GlobalTheory.SeparatedDirections.directions_typed_basis | exact GlobalTheory.SeparatedDirections.directions_typed_basis | (intros; apply GlobalTheory.SeparatedDirections.directions_typed_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTorsion_killed_by_prime_powers : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  first | exact @GlobalTheory.MomOne.smallTors | exact GlobalTheory.MomOne.smallTors | (intros; apply GlobalTheory.MomOne.smallTors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothCycOfKFinSmooth
section
noncomputable section

open Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothCyclicApprox

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.SmoothCyclic

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_expProd_entry {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp (contDiff_expProd Xs)

end

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smoothVec_of_smoothOnH {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) {v : H}
    (hv : PI.UpqRep.SmoothOnH G fun g => σ g v) : SmoothVec {X | Xᴴ * G + G * X = 0} σ v := by
  intro k Xs hX
  have hp : ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_expProd_entry Xs a b
  have hm : ∀ t : Fin k → ℝ, PI.UpqRep.inUH G (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := fun t =>
    list_prod_mem (G := G) _ fun g hg => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact exp_mem hG (hX i) _
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  obtain ⟨U, F, hU, htU, hF, hfF⟩ := hv _ (hm t)
  refine ((hF.contDiffAt (hU.mem_nhds htU)).comp t hp.contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [hp.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds htU)] with s hs
  exact hfF _ hs (hm s)

end

end GlobalTheory.SmoothCyclicApprox
end
end

