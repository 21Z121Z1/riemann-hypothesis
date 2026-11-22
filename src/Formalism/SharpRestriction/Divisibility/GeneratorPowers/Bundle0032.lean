import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0031
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def EtVal (X : WeightAlgebra.PJ D B P j) (i : ℕ)
    (η : B.Cusp j (WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩))) : Prop :=
  ∀ la (y : X.Pt la), ((2 * i * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ η)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

def nuWWOf {L : SizeData₂ D} {P : ParameterChoice' D L} (T : Top D) (Tp : ParamsT D L P) (hK : DV.KapDef D) (j : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ℝ :=
  letI := T.Q.H.starRing
  (nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la : ℝ)

def H1algStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (j : ℕ) (hj : InR D j),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (letI := T.Q.H.starRing; ChartSaturated (T.Q.Xo j) T.Q.c) →
    (∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) →
    (∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧
      ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x) →
    WeightAlgebra.H3 L H C2 A2 CR 0 (lR Tp hK j) Tp.TO →
    (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
        (2 * Module.finrank ℚ D.host.E) ≤ WeightFamilies.RRv D CR →
    (2 * D.R.f * D.R.m : ℝ) ^ 4 * Tp.nWn + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2 →
    D.R.f * D.R.r * (D.R.r + 1) ≤ Tp.nWn →
    (∀ i, (WeightAlgebra.DF (lR Tp hK j) : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ)) →
    ∀ la (y : (recPJ h j hj).Pt la),
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).S.sW (lR Tp hK j) la y ≤
        (((runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la +
          WeightAlgebra.cc D L C2 A2 CR (lR Tp hK j) * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

def HarmKillJetSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S),
    (∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1) →
    (∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)

namespace HarmInvPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem tie_val (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : IsExpOf C.B.G.F C.uvec φ) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k f P = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
      ∏ b, expVal (compL φ (f b * FB.expS S ((k : S) • C.B.hL S C.h H.w0))) (colOf m b) := by

  have hFK : C.B.FK S = C.B.G.F := by
    funext i
    first
      | simp [FB.FK, FGLaw.mapF]
      | (ext n; simp [FB.FK, FGLaw.mapF, MvPowerSeries.coeff_map])
  have hφ' : IsExpOf (C.B.FK S) C.uvec φ := by
    rw [hFK]
    exact hφ
  unfold chartVal
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  exact tie_alg (C.B.FK S) C.uvec φ hφ' (colOf m b) _

theorem cc_diagL {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (diagL B w0 cc) = 0 := by

  have hpt : ∀ {n : ℕ} (j : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
    intro n j i
    simp [pt]

  have hlg : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (lg B.G j i) = 0 := by
    intro j i
    exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev
      (fun j' i' => by
        fin_cases j'
        first
          | exact hpt j i'
          | simp [pt])
      ((HarmInvB.logOf_props B.G).1 i)
  unfold diagL
  refine ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev ?_ ?_
  · intro j i
    fin_cases j
    · first
        | exact hpt 0 i
        | simp [pt]
    · exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_ev
        (fun j' i' => by
          fin_cases j'
          first
            | exact hpt 0 i'
            | simp [pt])
        (B.A.const w0 i)
  · unfold bilL
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    first
      | simp [hlg]
      | simp [hlg, MvPowerSeries.smul_eq_C_mul]
      | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
            MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hlg]
         simp)

end HarmInvPf

open HarmInvPf in

theorem harmInv_of_kill (hK : HarmKillJetSt) (hA : ExpActOfSt) : HarmInvSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C cc hsym hbal k n D f f' hj a P hP hD
  obtain ⟨h0, h1, hadd⟩ := HarmInvB.logOf_props C.B.G
  obtain ⟨ε, hinv, htr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.formal_exp_law S C.d C.B.G (fun i => logOf C.B.G i) h0 h1 hadd
  have hφ := isExpOf_expPhi C.B.G C.uvec (fun i => logOf C.B.G i) ε h1 hinv htr
  set φ := ExpOf.expPhi C.uvec ε with hφdef
  set t : Fin 1 × Fin (dL Dw) → S := fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 H.w0) with ht
  have hta : ∀ q, MvPowerSeries.constantCoeff
      (t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) = 0 :=
    fun q => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act H.w0 j) =
      MvPowerSeries.subst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j) :=
    fun j => hA E H Dw l Xo c S y C φ hφ H.w0 j
  have hcd : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (diagL C.B H.w0 cc) =
      ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t) := by
    have e := HarmInvB.compL_diagL C.B H.w0 cc C.uvec ε hinv _ hta hact
    rw [HarmInvB.quad_form] at e
    exact e
  have hφs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin C.d => φ p.2) :=
    HarmInvB.hasSubst0 fun p => hφ.const p.2
  have hccd : MvPowerSeries.constantCoeff ((k : S) • diagL C.B H.w0 cc) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_diagL, mul_zero]
  set EL := FB.expS S ((k : S) • C.B.hL S C.h H.w0) with hEL
  have hjet : ∀ b, psJet D (compL φ (f' b * EL)) = psJet D (compL φ (f b * EL) *
      PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
        (PowerSeries.exp S)) := by
    intro b
    have e1 : psJet D (f' b * EL) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) := by
      rw [FBIdJet.psJet_mul, hj b, ← FBIdJet.psJet_mul]
    have e2 := HarmInvA.psJet_subst_congr D (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2) e1
    have e3 : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2)
        (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) = compL φ (f b * EL) *
          PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
            (PowerSeries.exp S) := by
      rw [MvPowerSeries.subst_mul hφs, MvPowerSeries.subst_mul hφs, expP,
        HarmInvA.subst_exp _ (fun p => hφ.const p.2) _ hccd, MvPowerSeries.subst_smul hφs, hcd, compL,
        MvPowerSeries.subst_mul hφs]
      ring
    exact e2.trans (congrArg (psJet D) e3)
  have hβ : ∀ i j, HarmInvB.qβ cc C.uvec t i j ≠ 0 →
      ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j hne
    refine hbal ((ltIdx Dw).symm i) ((ltIdx Dw).symm j) fun h0' => hne ?_
    have e : HarmInvB.qβ cc C.uvec t i j = (∑ a, ∑ b, cc a b * C.uvec ((ltIdx Dw).symm i) a *
        C.uvec ((ltIdx Dw).symm j) b) * t (0, j) := by
      simp only [HarmInvB.qβ, Finset.sum_mul]
    rw [e, h0', zero_mul]
  rw [tie_val C φ hφ k f' P, tie_val C φ hφ k f P]
  exact hK E H Dw l c S k n D (fun b => compL φ (f b * EL)) (fun b => compL φ (f' b * EL))
    (HarmInvB.qβ cc C.uvec t) hβ hjet a P hP hD

theorem harmInv_of (hA : ExpActOfSt) : HarmInvSt :=
  harmInv_of_kill (fun _ _ _ _ _ _ _ c _ _ _ _ k n D g g' β hβ hj a P hP hD =>
    HarmInvC.harm_kill_jet c k n D g g' β hβ hj a P hP hD) hA

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

open Classical in

def clOf {j : ℕ} (wL : WeightFamilies.Wt D j) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if ((D.host.QS : ℕ) : 𝓞 K) ∈ la.asIdeal then (padicValNat (ringChar (𝓞 K ⧸ la.asIdeal)) D.host.QS : ℝ) * (c2 D wL : ℝ)
  else if ((D.host.q : ℕ) : 𝓞 K) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 K) ∈ la.asIdeal then (cHalf wL : ℝ)
  else 0

def RStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (nuWW : ℕ → HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ)
    (j : ℕ) (hj : InR D j) (RR PP qmin : ℝ),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (T.Q.l.M : ℕ) = D.host.g 0 * D.host.g 1 →
    D.host.rdE ^ 2 / (4 * D.R.f) ≤ RR →
    ((2 * D.R.f * D.R.m : ℕ) : ℝ) ^ 3 ≤ PP →
    0 < qmin → qmin ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) →
    (WeightAlgebra.DF (lR Tp hK j) : ℝ) * 2 * Real.sqrt ((2 * D.R.f * D.R.m : ℕ) : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) →
    4 * WeightAlgebra.DF (lR Tp hK j) + 4 ≤ D.host.g 0 * D.host.g 1 →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)),
    (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ (y : (recPJ h j hj).Pt la) (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (_ : OverLa la T'.V io e)
      (z : IntFr (T.Q.Xo j) T.Q.c T' io) (_ : z.IsAlg) (eta : T.G.PY j (WeightAlgebra.resCh la)) (_ : T.G.lies j la T' io z eta),
      (show T.PtA j la from y).1 = profI (T.Q.Xo j) T.Q.c (T.G.PY j (WeightAlgebra.resCh la)) e z eta →
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX nuWW j).S.sW (lR Tp hK j) la y ≤
        (letI := T.Q.H.starRing; nuLoc z e T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn) +
          (((ramOverZ la : ℝ) * clOf (lR Tp hK j) la +
            RR * PP * (WeightAlgebra.DF (lR Tp hK j) : ℝ) ^ 2 / qmin * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

