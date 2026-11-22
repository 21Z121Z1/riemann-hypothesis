import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0108
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0183
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0131
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0110
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0095
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0841
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3352

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColSide
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.Fam.colSide_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA k row hrow hsame
  classical
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  have hc : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row _root_.GlobalTheory.Fam.trivialColumnChoice) (hRow _)).1
  choose J hJ using _root_.GlobalTheory.T.exists_quadratic_extension_reads_of_true W hW u a ha haT hc
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt W hW u a ha haT hiA
  choose s ζ ρ hD using fun t => hC t (J t) (hJ t)
  obtain ⟨V, VT, hV0, hVT0, hV⟩ := _root_.GlobalTheory.T.true_geometry_exists_volume_data_alt W hW u a ha haT
  obtain ⟨kom, hkom⟩ := _root_.GlobalTheory.T.true_geometry_exists_kernel_alt W hW u a ha haT
  have hdd0 : ∀ t j α γ, ∃ d, j < B.R.m → GlobalTheory.SeeSaw.IsFinComb d ∧ ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d f =
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((J t).dQ (s t) j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f)) := by
    intro t j α γ
    by_cases hj : j < B.R.m
    · obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_twist_local_value_alt W hW u a ha haT t (J t) (hJ t) (s t) j α γ hj
      obtain ⟨d, hd⟩ := GlobalTheory.Fam.finComb3 _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ _ h1 h2 h3
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose dd hdd using hdd0
  obtain ⟨S', hS'⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt W hW u a ha haT J hJ k
  have hone : ∀ t, ∃ β₀ : (J t).Ch B.R.m, ∀ β, β = β₀ := fun t => by
    have hc1 : Fintype.card ((J t).Ch B.R.m) = 1 := by
      rw [Fintype.card_pi]
      refine Finset.prod_eq_one fun i _ => ?_
      have h1 := ((J t).E i).one
      have h2 : ((J t).G i).s + 1 + 1 = B.R.m := ((J t).G i).hs
      rw [h2] at h1
      exact h1
    exact Fintype.card_eq_one_iff.1 hc1
  choose β₀ hβ₀ using hone
  let cQf : W.P.T → ℕ → ℂ := fun t j => ∏ i, ((((J t).E i).idx (j + 1) : ℂ) * (((J t).E i).idx (j + 1 + 1) : ℂ))⁻¹
  let cTf : W.P.T → ℕ → ℂ := fun t j => @TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
  let cK : W.P.T → ℕ → ℂ := fun t j => V j * C j * a.c₀ j * ρ t j
  let cP : W.P.T → ℂ := fun t => VT * ∑ β, s t B.R.m β
  let cV : W.P.T → ℕ → ℂ := fun t j => if h : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then
      k.v.kap j h.choose h.choose_spec * (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
    else (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
  let col := _root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP
  let F := _root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col (fun _ => rfl)
  let w₀ := fun t => (F t).pinTup (k.sc t) (cTf t)
  let w := fun t => GlobalTheory.QTw.resc (w₀ t) (s t)
  have hPinCh : ∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) a.c₀ (J t).A (J t).ι w := fun t => by
    refine ⟨fun j α γ => C j * (J t).wt j α * ζ t j α γ, ?_⟩
    refine
      { is := (hJ t).is
        live := (hJ t).live
        om := fun j hj => by rw [(hJ t).chr j hj]; exact hkom t j hj
        dat := fun j hj α γ => ⟨(hdd t j α γ (by omega)).1, by
          show IsRatDatum _ _ _ _ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (dd t j α γ) (a.g.vac j))
          rw [(hdd t j α γ (by omega)).2]
          exact ((hD t).2.2.2 j hj α γ).1⟩
        cst := fun j hj α γ _ => by
          have h1 := ((hV t (J t) (hJ t)).1 j (by omega) α)
          have h2 := ((hD t).2.2.2 j hj α γ).2
          show V j * C j * a.c₀ j * ρ t j = _
          rw [← h1, ← h2]
          ring
        ram := fun j _ φ => Iff.rfl
        rdq := fun j hj β φ y => dif_pos hj }
  refine ⟨col, w₀, w, F, ⟨a.c₀, haT.pinX, fun t => ⟨⟨(J t).Ch₀, (J t).A, (J t).ι, hPinCh t⟩, ?_⟩⟩, ?_⟩
  · obtain ⟨UT, hUT1, hUT2⟩ := (hV t (J t) (hJ t)).2
    refine ⟨UT, s t B.R.m (β₀ t) * (J t).wt B.R.m (β₀ t),
      { emb := haT.emb
        lev := hUT1
        eT := fun n h β => ?_
        cP := ?_ }⟩
    · subst h
      rw [hβ₀ t β]
      show (s t B.R.m (β₀ t) • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt B.R.m (β₀ t))).mapDomain (· * a.g.bT) = _
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, one_mul, smul_eq_mul]
    · show VT * ∑ β, s t B.R.m β = _
      rw [Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb), ← hUT2 (β₀ t)]
      ring
  have hdQ : ∀ t j α γ, j < B.R.m → (w t).dQ j α γ = (J t).dQ (s t) j α γ := fun t j α γ hj => by
    show _ • (if j < B.R.m then _ else 0) = _
    rw [if_pos hj]
    rfl
  have hpl := fun t => _root_.GlobalTheory.T.true_geometry_twist_local_data_alt W hW u a ha haT t (J t) (hJ t)
  have hQ : ∀ t p, p ∈ (w₀ t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := fun t p => by
    show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, (hpl t).2 i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, hi⟩ := (hJ t).surj PP hPP
      exact ⟨i, Finset.mem_univ _, by rw [(hpl t).2 i, hi]⟩
  have hPins : ∀ t, (F t).Pins (w₀ t) := fun t =>
    { inj := (hpl t).1
      places := fun p => by
        show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
        rw [Finset.mem_image]
        exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
      kom := fun j hj => hkom t j hj
      mid := fun j σ h => ⟨(_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, ((hrow t).sBF j (σ + 1) h).2.2.1, ((hrow t).sBF j (σ + 1) h).2.2.2,
        ((hrow t).sFB j σ h).2.2.1, ((hrow t).sFB j σ h).2.2.2⟩
      lastc := fun j h => ((hrow t).sBF j 0 h).2.2.2
      eQ := fun j hj => if_pos hj
      eQT := fun j h => rfl
      dQ := fun j hj α γ => if_pos hj
      ε := fun j ρ' h α => if_pos (Or.inl ⟨ρ', h⟩)
      εT := fun n h β => rfl
      FY := fun j _ f hf => hf
      cQ := fun j _ => rfl }
  have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
    have h1 := ha.vis.bT
    rw [((ha.tie row col).1.bT).1] at h1
    exact h1
  have hOK : (a.fam row col).ColOK :=
    { kom := fun t j hj => hkom t j hj
      ker := fun t j hj α γ => by
        have hx := haT.pinX.xs j (by omega)
        have hx' := haT.pinX.xs (j + 1) (by omega)
        have hL : ((a.g.x j).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx.2.2 z)
        have hL' : ((a.g.x (j + 1)).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx'.2.2 z)
        have hv : IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ (a.g.x j).s (a.g.x (j + 1)).s ((a.g.x j).L : Set _)
            ((a.g.x (j + 1)).L : Set _) (a.g.vac j) := by
          rw [hx.1, hx'.1, hL, hL']
          exact haT.pinX.vc j hj
        exact ⟨⟨_, _, hkom t j hj⟩, hv, (hdd t j α γ hj).1⟩
      e := fun t j α g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        exact (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α x (Finsupp.support_smul hx)).2
      eT := fun t n h β g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        have : x = 1 := by
          exact Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hx))
        subst this
        simpa using hbT
      stabK := fun t j hj ψ hψ => GlobalTheory.T.chainKernel_preserves_ramifiedForms_liveCharts I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) (J t).Ch₀ (J t).Ch (J t).A (J t).ι
        (hJ t).is (hJ t).live j hj ψ hψ
      stabS := fun t j hj ψ hψ => (hS' t).1 j hj (k.ε j) ψ hψ }
  have hcv : ∀ t, CVEq k.v (w t) := fun t => by
    refine ⟨fun j σ h => ?_, fun j h => ?_⟩
    · have hex : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := ⟨σ, h⟩
      have hk : ∀ σ' (h' : j + 2 * (σ' + 1) + 2 = B.R.m), k.v.kap j σ' h' = k.v.kap j σ h := fun σ' h' => by
        obtain rfl : σ' = σ := by omega
        rfl
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_pos hex, hk]
      rfl
    · have hex : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := fun ⟨σ, h'⟩ => by omega
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_neg hex]
      rfl
  have hroot : ∀ (Sp : ℕ → Prop) (x : ℂ), (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → ∀ y : ℂ, (∃ n : ℕ, 0 < n ∧ y ^ n = 1) → ∀ c : ℂ, c ≠ 0 →
      GlobalTheory.Fam.UnitRatio Sp (c * x) (c * y) := fun Sp x ⟨n1, hn1, hx⟩ y ⟨n2, hn2, hy⟩ c hc => by
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hy
      exact zero_ne_one hy
    refine (GlobalTheory.Fam.unitRatio_laws Sp).2.2.1 _ _ (n1 * n2) (mul_ne_zero hc hy0) (Nat.mul_pos hn1 hn2) ?_
    rw [mul_pow, mul_pow, pow_mul x, hx, pow_mul' y, hy, one_pow, one_pow]
  have hsum : ∀ t, ∑ β, s t B.R.m β = s t B.R.m (β₀ t) := fun t =>
    Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb)
  refine
    { ok := hOK
      pins := hPins
      same := fun t => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      laws := fun t => _root_.GlobalTheory.T.true_geometry_family_final_alt hDS hHC W hW u a ha haT row col (hRow col) hOK t (F t) (w₀ t) (s t) (hD t).1 (hPins t) (hQ t)
      lev := fun t => _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt W hW u a ha haT t (J t) (hJ t) row col (F t) rfl rfl (fun i => HEq.rfl)
      vec := fun t => _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) _ t
      FY := fun t j f => Iff.rfl
      FT := fun t f => Set.mem_univ f
      FX := fun t j _ ψ _ α y => Set.mem_univ _
      atQ := fun t j => by
        obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j
        refine ⟨h1, h2, fun α γ x hx => h3 α γ x (Finsupp.support_smul hx)⟩
      e := fun t j α => ⟨rfl, fun g hg => (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α g (Finsupp.support_smul hg)).1⟩
      eT := fun t n h β => ⟨rfl, fun g hg => by
        have hg' := Finsupp.support_single_subset (Finsupp.support_smul hg)
        rw [Finset.mem_singleton.1 hg']
        exact Subgroup.one_mem _⟩
      dd := fun t j hj α γ f _ => by
        rw [hdQ t j α γ hj]
        exact (hdd t j α γ hj).2 f
      read := fun t => ⟨S' t 0, (hS' t).2 row kom dd s cV cK cP⟩
      sc := fun t => rfl
      cT := fun t j ρ' h => (congrArg (@TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j)) ((hrow t).sBF j ρ' h).2.2.2).symm
      cv := hcv
      cK := fun t j hj => hroot _ _ ((hD t).2.2.1 j) _ ((hD _).2.2.1 j) _
        (mul_ne_zero (mul_ne_zero (hV0 j hj) (hC0 j hj)) (haT.pinX.mv j (by omega)).1)
      cP := fun t => by
        show GlobalTheory.Fam.UnitRatio _ (VT * ∑ β, s t B.R.m β) (VT * ∑ β, s _ B.R.m β)
        rw [hsum, hsum]
        exact hroot _ _ ((hD t).1 _ _) _ ((hD _).1 _ _) _ hVT0
      zero := _root_.GlobalTheory.T.true_geometry_joint_twist_bound_alt W hW u a ha haT J hJ row kom dd _ s cV cK cP (fun t α => (hD t).2.1 α) hPinCh }
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InputsOfSidesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inputs_of_galHodgeN_roots : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D, (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∃ N0, Inputs D E N0 := by
  first | exact @_root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge | exact _root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge | (intros; apply _root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnitStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_ratio_realization_same_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | exact _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvNEa
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy
def witDropA_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {A : AtP} {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s K w Z O) : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, x.nx.2.1⟩ }
theorem slot_mv_extension_with_at_property {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} (A : AtP)
    (hs : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  intro K B f T w Z O x Nd h O' hO' col n
  obtain ⟨t, hobj, hrx, ⟨c⟩, hsx, hox⟩ := hs K B f T w Z O (_root_.GlobalTheory.Mem.LiteralAutomorphy.witDropA_alt x) Nd h O' hO' col n
  exact ⟨t, hobj, hrx, ⟨⟨c.1, c.2, x.nx.2.2⟩⟩, hsx, hox⟩
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lower_bound_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistLowerBound := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twGe_alt | exact _root_.GlobalTheory.BigOn.Exp.twGe_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twGe_alt <;> assumption)
end
end

