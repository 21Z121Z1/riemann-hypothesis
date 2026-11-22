import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardFormComparisonSymmetricLevelMember
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem hform_last {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (hN : 0 < N) {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1) {p : E}
    {z : Fin N → E} (hz : ∀ j, z j = if j.1 + 1 = N then p else 0) (x : Fin N → E) :
    hform σ J z x = σ p * x ⟨N - 1, by omega⟩ := by
  obtain rfl : z = fun j => if j.1 + 1 = N then p else 0 := funext hz
  subst hJ
  unfold hform
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single ⟨N - 1, by omega⟩]
  · simp [show N - 1 + 1 = N by omega]
  · intro b _ hb
    have : ¬ (b.1 + 1 = N) := fun h => hb (Fin.ext (by simp; omega))
    simp [this]
  · simp

theorem sigD_conj (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = D.host.conj x := by
  first | rfl | exact Formalism.BasicNotions.Examples₂.star_eq_conj _ _

set_option maxHeartbeats 4000000 in

theorem formsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) ∧ (∀ u i, Finite (Ch u i)) ∧ (∀ u, Nonempty (Unique (Ch u B.R.m))) ∧ (∀ u u', (F u).gl = (F u').gl) ∧ CharacterCompatible (F B.u₀).gl B.R.m := by
  intro B X I hOk hPins l Z
  obtain ⟨G, hG, hChi⟩ := GlobalTheory.Mem.TypePrimes.exists_gLoc_idG_chiTied I hOk hPins l Z
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z

  have hch : ∀ (u : B.Word) (i : ℕ), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch)
      (K : ∀ (hi : i ≤ B.R.m) (β : Ch), LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi
        (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))),
      (∀ hi, I.ReadsK l Z u I.mu0 i hi chOf (K hi)) ∧ (∀ hi c, ((K hi (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧
      ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) ∧ ∀ hi β, FunKilled (K hi β).lev (X.piT u) := by
    intro u i
    by_cases hi : i ≤ B.R.m
    · obtain ⟨Ch, hF, chOf, K, h1, h2, h3⟩ := GlobalTheory.Mem.Col2.MemChart.exists_charts I hOk hPins l Z u i hi
      obtain ⟨K', h4, h5⟩ := GlobalTheory.Mem.Col2.TC.charts_funKilled I hOk hPins l Z u I.mu0 i hi _ Ch chOf K h1
      refine ⟨Ch, hF, chOf, fun _ => K', fun _ => h4, fun _ c => ?_, h3, fun _ β => (h5 β).1⟩
      rw [(h5 (chOf c)).2.2.2.2.2.1]
      exact h2 c
    · refine ⟨Unit, inferInstance, fun _ => (), fun h => absurd h hi, fun h => absurd h hi, fun h => absurd h hi, fun h => ?_, fun h => absurd h hi⟩
      exfalso
      rcases h with h | h <;> omega
  choose Ch hChF chOf K hRK hYs hU hFK using hch
  have hYs' : ∀ u i hi β c (e : chOf u i c = β), ((K u i hi β).y ⟨c, e⟩).1 = I.yStd u i c := by
    intro u i hi β c e
    subst e
    exact hYs u i hi c
  let A : ∀ u, AtTTied (D := I.rec7 l Z) u := fun u => GlobalTheory.Mem.AtLevel.atTTied I l Z u
  have hIdV : ∀ u, I.IdV l u I.mu0 (A u).eV := fun _ _ => rfl
  choose eY hIdY hde using fun u i (hi : i ≤ B.R.m) => ((hN i hi).2.2 u I.mu0).2
  choose Lv hLv using fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.exists_level_projections I hOk hPins l Z u I.mu0 i hi
  have hde1 : ∀ u i (hi : i ≤ B.R.m), ∃ C : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E,
      cT (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) C.1 * C.1 = gramN (I.rec7 l Z) i hi ∧
      (∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔
        ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range) ∧
      ∀ τ z, ((I.rec7 l Z).mem u).C.de i z τ = embT (I.rec7 l Z) τ C.1.det * ((eY u i hi z).1 τ).det := by
    intro u i hi
    refine ⟨1, ?_, fun x => ?_, fun τ z => ?_⟩
    · rw [(hN i hi).1]
      simp [cT]
    · rw [Units.val_one]
      simp only [Matrix.one_mulVec]
      exact (hN i hi).2.1 x
    · refine (hde u i hi τ z).trans ?_
      rw [Units.val_one, Matrix.det_one, map_one, one_mul]
  have hVG := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.val_tied I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (hRK u i hi) (hIdY u i hi)
  have hIN := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)
  have hNm : ∀ u i hi, NormTieG (D := I.rec7 l Z) ((I.rec7 l Z).fm u) (eY u i hi) := fun u i hi => (hIN u i hi).2
  have hDil := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.DiaChart.dilTied I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (hRK u i hi) (hFK u i hi) (hIdY u i hi) (hIdV u)
  choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.LevFun.fvTieG I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
    (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdV u) (hLv u i hi) (hFK u i hi)
  have hUp := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.UpChart.upNatTie I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hDn := fun u i (hi : i ≤ B.R.m) => GlobalTheory.DnMove.dnNatTieG_cols I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hBw := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.bw_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)

  have hHex : ∀ u i (β : Ch u i), ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
      ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Subgroup (GL (Fin (B.R.N i)) (kv (I.rec7 l Z).host.F v)))
      (lam : ∀ j v h, H j v h →* ℂˣ), ∀ hi : i ≤ B.R.m, Nonempty (GLevH (K u i hi β).lev G H lam) := by
    intro u i β
    by_cases hi : i ≤ B.R.m
    · obtain ⟨H, lam, h⟩ := GlobalTheory.Mem.Col2.ChartLevel.chart_gLevH I hOk hPins l Z u G i hi (Ch u i) (chOf u i) (K u i hi) hG (hRK u i hi) β
      exact ⟨H, lam, fun _ => h⟩
    · exact ⟨fun _ _ _ => ⊤, fun _ _ _ => 1, fun h => absurd h hi⟩
  choose Hc lamC hGH using hHex

  choose J lamJ VJ Yb hYbF hYbA yb hJ using fun u => GlobalTheory.Mem.Col2.OneLevel.stepBefore_oneLevel I hOk hPins l Z u G (Ch u (B.R.m - 1))
    (chOf u (B.R.m - 1)) (K u (B.R.m - 1) (Nat.sub_le _ _)) hG (hRK u _ _)

  choose KP WP hKP using fun u => GlobalTheory.Mem.Col2.TC.clsP_tie I hOk hPins l Z u

  choose jM hjM using fun u => GlobalTheory.Mem.Col2.PerConj.period_conj I hOk hPins l Z u I.mu0

  let β0 : ∀ u i, (i = 0 ∨ i = B.R.m) → Ch u i := fun u i h => (hU u i h).some.default
  have hβ0 : ∀ u i h c, chOf u i c = β0 u i h := fun u i h c => (hU u i h).some.uniq _
  have hSub : ∀ u i, (i = 0 ∨ i = B.R.m) → Subsingleton (Ch u i) := fun u i h => @Unique.instSubsingleton _ (hU u i h).some
  let clsF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ClsTied (D := I.rec7 l Z) u i hi := fun u i hi h =>
    clsOfChart (β0 u i h) (hβ0 u i h) (K u i hi (β0 u i h))
  let valF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ValTied (D := I.rec7 l Z) u (A u).eV i hi (clsF u i hi h) := fun u i hi h =>
    @valOfG _ u i hi (Ch u i) (chOf u i) (hSub u i h) (A u).eV (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (hde1 u i hi)
      (hVG u i hi) (hIN u i hi).1 (hDil u i hi)
  have hR : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => (clsF u i hi h).lev.Lb)
      (fun _ => (clsF u i hi h).lev.U) (fun _ => (clsF u i hi h).lev.chi) (fun c => ((clsF u i hi h).y c).1)
      (fun c s => ((clsF u i hi h).stabI c s).1) k :=
    fun u i hi h => readsK_one I l Z (hRK u i hi) (β0 u i h) (hβ0 u i h)
  choose V0 hV0 using fun u => GlobalTheory.Mem.Col2.TC.GLev0.glev_zero I hOk hPins l Z u G (clsF u 0 (Nat.zero_le _) (Or.inl rfl)) hG
    (hR u 0 _ (Or.inl rfl))
  choose lamM lamP VM VP hVM using fun u => GlobalTheory.Mem.Col2.TC.levels_top_row_sym I hOk hPins l Z u G (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u) hG
    (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
  choose Tl Ta hTl using fun u => GlobalTheory.Mem.Col2.TC.til_ties I hOk hPins l Z u (A u) (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u)
    (lvOfG (A u) (Lv u B.R.m le_rfl)) (valF u B.R.m le_rfl (Or.inr rfl)) rfl (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
    (fun v c z h => (hLv u B.R.m le_rfl).1 v c z h) (hIdY u B.R.m le_rfl)
  choose eW heW hEvz using fun u => (hTl u).2.2
  have hNpos : 0 < B.R.N B.R.m := by
    have := k_le_N B.R B.R.m
    have := B.R.m_add_three_le_k
    omega
  have hTilFv : ∀ u, TilBaseFv (Tl u) (clsF u B.R.m le_rfl (Or.inr rfl)) (fun v => fMe u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v) := by
    intro u v t x r ht hr
    refine hFvT u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v x ⟨B.R.N B.R.m - 1, by omega⟩ r t (by show B.R.N B.R.m - 1 + 1 = _; omega) ht ?_
    refine hr.trans ((hform_last _ hNpos (hN B.R.m le_rfl).1 (hTl u).1 x).trans ?_)
    exact congrArg (fun s : B.host.E => s * (show B.host.E from x ⟨B.R.N B.R.m - 1, Nat.sub_lt hNpos Nat.one_pos⟩)) (sigD_conj (I.rec7 l Z) _)
  have hFrExt : ∀ u, FrExtFr (D := I.rec7 l Z) (Tl u).z0 G (VM u).fr (VP u).fr := by
    intro u
    rw [funext (hTl u).1]
    exact (hVM u).2.2.2
  let F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u) := fun u =>
    { atT := A u
      gl := G
      gl_K := fun i => by rw [hG.piG]; exact X.piG_K i
      cls := clsF u
      val := valF u
      glev0 := V0 u
      lamM := lamM u
      lamM_eq := (hVM u).1
      glevM := VM u
      lv := fun i hi => lvOfG (A u) (Lv u i hi)
      fMe := fun i hi h v => fMe u i hi (β0 u i h) v
      fv := fun i hi h => fvOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (fMe u i hi) (hFv u i hi)
      upN := fun i hi h => upOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hUp u i hi)
      dnN := fun i hi h => dnOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hDn u i hi)
      norm := fun i hi h => (normOfG (D := I.rec7 l Z) (u := u) (eY u i hi) (valF u i hi h) rfl (hNm u i hi) :)
      bw := fun i hi h => bwOfG (A u) (eY u i hi) (valF u i hi h) rfl (hBw u i hi)
      ch := fun i _ h2 β => K u i (le_of_succ_m h2) β
      H := Hc u
      lamC := lamC u
      glevC := fun i _ h2 β => (hGH u i β (le_of_succ_m h2)).some
      eYC := fun i _ h2 => eY u i (le_of_succ_m h2)
      deC := fun i _ h2 => hde1 u i (le_of_succ_m h2)
      valC := fun i _ h2 => hVG u i (le_of_succ_m h2)
      ipVC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).1
      normC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).2
      dilC := fun i _ h2 => hDil u i (le_of_succ_m h2)
      lvC := fun i _ h2 => Lv u i (le_of_succ_m h2)
      fMeC := fun i _ h2 => fMe u i (le_of_succ_m h2)
      fvC := fun i _ h2 => hFv u i (le_of_succ_m h2)
      upC := fun i _ h2 => hUp u i (le_of_succ_m h2)
      dnC := fun i _ h2 => hDn u i (le_of_succ_m h2)
      bwC := fun i _ h2 => hBw u i (le_of_succ_m h2)
      levJ := J u
      lamJ := lamJ u
      lamJ_eq := (hJ u).2.1
      glevJ := VJ u
      Yb := Yb u
      YbFin := hYbF u
      YbAct := hYbA u
      yb := yb u
      yb_orbit := (hJ u).2.2.1
      levJ_Lb := fun _ β => ((hJ u).2.2.2 β).1
      levJ_le := fun _ β => ((hJ u).2.2.2 β).2.1
      levJ_stab := fun _ β => ((hJ u).2.2.2 β).2.2.1
      levJ_chi := fun _ β => ((hJ u).2.2.2 β).2.2.2
      clsP := KP u
      valP := WP u
      normP := (hKP u).2.1
      lamP := lamP u
      eigenvalue_eq₂ := (hVM u).2.1
      glevP := VP u
      til := Tl u
      tilLat := (hTl u).2.1
      tilFv := hTilFv u
      tilAd := Ta u
      frExt := hFrExt u
      eWz := eW u
      evz := hEvz u
      jM := jM u
      per := ⟨(hjM u).2.1, (hjM u).2.2.1, (hjM u).2.2.2.1⟩
      DGam := rfl }
  refine ⟨Ch, chOf, F, fun u => ⟨?_, ?_⟩, hChF, fun u => hU u B.R.m (Or.inr rfl), fun _ _ => rfl, hChi⟩
  · exact
      { eV := fun _ => rfl
        piU := rfl
        res := rfl
        gl := hG
        ends := fun i hi h => hR u i hi h
        yE := fun i hi h c => hYs' u i hi _ c (hβ0 u i h c)
        mid := fun i _ h2 => hRK u i (le_of_succ_m h2)
        eY := fun i hi _ => hIdY u i hi
        eYC := fun i _ h2 => hIdY u i (le_of_succ_m h2)
        pr := fun i hi => (hLv u i hi).1
        prk := fun i hi => (hLv u i hi).2
        fr0 := hV0 u
        frP := (hVM u).2.2.1
        what₂ := (hKP u).1
        eW := (hKP u).2.2
        z0 := (hTl u).1
        eWz := heW u }
  · exact ⟨fun i _ h2 => hLv u i (le_of_succ_m h2), (hJ u).1⟩

end GlobalTheory.Mem.FormSym

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEqStatement
section
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentTriangular_of_periodCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  first | exact @GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | exact GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | (intros; apply GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotropicRankIwasawaDecomposition

theorem finrank_isot_eq_isotL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (D.what₂.isot ((i : ℕ) + 1) π) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y i π
  have hle : Y.IL.prtW i π ≤ (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [Y.prtWE]
    exact Submodule.map_mono inf_le_left
  have e1 : D.what₂.isot ((i : ℕ) + 1) π =
      ((Y.IL.prtW i π).comap ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i).subtype).comap
        (Y.IL.jMj i).toLinearMap := by
    ext y
    exact Y.tied.lift.isot i π y
  rw [e1, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, Y.prtWE]
  exact LinearEquiv.finrank_map_eq PiTensorProduct.lift _

end GlobalTheory.Mem.R3.IsotropicRankIwasawaDecomposition

namespace GlobalTheory.Mem.R3

theorem isotRank_of_multEq : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.BasicNotions.Rows.IsotRank D.what₂ := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost hX hD hM j hj1 hj2 π
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [IsotropicRankIwasawaDecomposition.finrank_isot_eq_isotL D G Pl0 I0 T A3 Ks R F cG X0 Y i π,
    ← GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hX hD hM i π,
    GlobalTheory.T.baseRowCount_eq_finrank_typePart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost π]

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  first | exact @GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | exact GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | (intros; apply GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsLOfCopy
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.DatCopy

namespace GlobalTheory.Mem.R3.LiftCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} {R : RealDat3 a.D A Ks} {F : Face3 a.D A}

theorem holdsL_tr (h : HoldsL R F) : letI := alg b iK; HoldsL (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke => tr_via (fun X : Cx.CxData A.fam3.amb3 => (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW) (toCx3_eq b R F) h.hecke
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv => tr_via (fun u : Parts R => Cx.GEquiv3 A (cxW R F u) ((by with_unfolding_all exact ((R.gEx F) :))) ∧ Cx.LiftGroupEquivariance A (cxW R F u) ((by with_unfolding_all exact ((R.gWx F) :)))) (parts_eq b R F) h.gEquiv
  case block => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock) (toCx3_eq b R F) h.block
  case liftTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X) (toCx3_eq b R F) h.liftTest
  case liftTestB => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false) (toCx3_eq b R F) h.liftTestB
  case liftOnto => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ hW, Cx.HeckeIntertwiningLifts A X hW →
      U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW) (toCx3_eq b R F) h.liftOnto
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.MLat false) (toCx3_eq b R F) h.mLat
  case levW => tr_via (fun u : Parts R =>
      Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gWx F) :))) false F.P0 F.ψ0) (parts_eq b R F) h.levW
  case thmA => tr_via (fun W : type_of% R.Wp3 => ∀ i t,
      Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.thmA
  case sumW => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false) (toCx3_eq b R F) h.sumW
  case aux => exact (by with_unfolding_all exact ((realAdelicInertTransport_furtherRows b h.aux) :))
  case ok => exact (by with_unfolding_all exact (h.ok :))
  case sep => exact (by with_unfolding_all exact (h.sep :))

theorem holdsL_back (h : letI := alg b iK; HoldsL (real3 b R) (face3 b F)) : HoldsL R F := by
  have h2 := holdsL_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => HoldsL R' F) (twice_eq b R).symm) ((h2))) : _))

end Three

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}
  (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem holdsL_of_copy (h : HoldsL (copy b s z).R (copy b s z).F) : HoldsL z.R z.F := holdsL_back b (iK := z.alg) ((by with_unfolding_all exact (h :)))

end Dat

end GlobalTheory.Mem.R3.LiftCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

abbrev refUp (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : Refill Z :=
  { Refill.ofDiv Z N h with S := S' }

open Formalism.BasicNotions.DivX (md) in
set_option maxHeartbeats 1000000 in

def divBack {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (X : DivX (w.D (SRe.upL Z S' N h))) : DivX (w.D Z) :=
  { X with md := fun S κ p _ la z => { md X S κ p la z with } }

set_option maxHeartbeats 1000000 in

theorem grpAt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GrpAt (w.st Z) w.I) : GrpAt (w.st (SRe.upL Z S' N h)) w.I :=
  ⟨(by with_unfolding_all exact (x.pl :)), (by with_unfolding_all exact (x.idem :)), (by with_unfolding_all exact (x.cen :))⟩

set_option maxHeartbeats 1000000 in

theorem muIsW_up {Z : w.Lt} {Wt : Set B.places.Pl} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (x : V4.MuIsW (w.st Z) f T Wt w.I.xi) : V4.MuIsW (w.st (SRe.upL Z S' N h)) f T Wt w.I.xi where
  inj := (by with_unfolding_all exact (x.inj :))
  range := (by with_unfolding_all exact (x.range :))
  mu0 := (by with_unfolding_all exact (x.mu0 :))
  star := (by with_unfolding_all exact (x.star :))
  star' := (by with_unfolding_all exact (x.star' :))
  tw := (by with_unfolding_all exact (x.tw :))
  on := (by with_unfolding_all exact (x.on :))
  off := (by with_unfolding_all exact (x.off :))
  sub := (by with_unfolding_all exact (x.sub :))
  supp := (by with_unfolding_all exact (x.supp :))

set_option maxHeartbeats 1000000 in

theorem rowInt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GlobalTheory.PerQ.RowInt w.I w.l Z) : GlobalTheory.PerQ.RowInt w.I w.l (SRe.upL Z S' N h) :=
  ⟨(by with_unfolding_all exact (x.ref :)), (by with_unfolding_all exact (x.tw :))⟩

set_option maxHeartbeats 1000000 in

theorem idxDefs_up {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (Y : DivX (w.D (SRe.upL Z S' N h))) (hI : IdxDefs (w.D Z) (divBack Y)) : IdxDefs (w.D (SRe.upL Z S' N h)) Y :=
  ⟨(by with_unfolding_all exact (hI.Ij_def :)), (by with_unfolding_all exact (hI.jw_def :))⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftIdentificationsOfLiftsComparisonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftIdentifications_of_liftsComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT | exact GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT | (intros; apply GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoicesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchTupleChartMemberChartStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.match_tupleChart_memberChart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∃ (c0f : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → (I.stp u I.mu0 i).Cl) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) ∧ (a = I.mu0 → ∀ β, t β = 1) ∧ ∀ β, ∃ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) → (∀ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ → ∃ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr (c0f β).1 κ0) ∧ (∀ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEvalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  first | exact @GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | exact GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | (intros; apply GlobalTheory.Mem.LocDictT.mem_locW_iff_delW <;> assumption)
end

