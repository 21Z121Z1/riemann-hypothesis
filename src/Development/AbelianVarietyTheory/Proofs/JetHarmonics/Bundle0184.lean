import Mathlib
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0136
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0182

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficients
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.HatNF.EmptyWordL2

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integrable_weight_normSq (hXi : B.XiExists) {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ)
    (hF : ∀ m : ℕ, B.InCC A m F) (hAB : B.AB k r ≤ A) (hT : JF.TransportedAlt k r A 0) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq D A hAB
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin := (hB1 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D A 0 F hT (hF 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (Formalism.FourierDecayAlt.P.B7.Q0 D) := h.continuousOn
  have h3 : ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (Formalism.FourierDecayAlt.P.B7.Q0 D) :=
    (LinearMap.continuous_of_finiteDimensional
      (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
        (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    Formalism.FourierDecayAlt.P.JCx2.rb_aesm D _ ((Formalism.FourierDecayAlt.P.JCx2.rb_contOn_bcW D).mul (h3.norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (Formalism.FourierDecayAlt.P.JCx2.rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem Ew_bigPt_eq_indicator {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      (Formalism.FourierDecayAlt.P.B7.Q0 p.T.base).indicator
        (fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
          ‖B.hsVec (B.JF p.T.base F (B.gq p.T.base q))‖ ^ 2)
        ((fun j => c j.castSucc), c (Fin.last P.r)) := by
  by_cases hq : ((fun j : Fin P.r => c j.castSucc), c (Fin.last P.r)) ∈ Formalism.FourierDecayAlt.P.B7.Q0 p.T.base
  · rw [Set.indicator_of_mem hq]
    obtain ⟨hc, hlt⟩ := hq
    dsimp only at hc hlt
    have hTT : 0 < Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := mul_pos p.T.base.T_pos p.T.base.T'_pos
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p F hl, Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · rw [Set.indicator_of_notMem hq]
    refine Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F fun h => hq ⟨fun a => ?_, ?_⟩
    · exact (h.1.1 (1, c a.castSucc) (by
        unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a.castSucc, rfl⟩)).2
    · exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c h.2

end

theorem integrable_density_nil_of_xiExists (hXi : B.XiExists) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p H A _ hCC hA
  have ha : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  set x : ℝ := (P.r : ℝ) + 1 with hx
  set n : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn
  have hx1 : 1 ≤ x := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : x * n ^ 2 ≤ x ^ 4 * n ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : 10 * (x * n ^ 2) ≤ A := by nlinarith
  have h5 : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have h6 : x * n ≤ x * n ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : 1 ≤ x * n := by nlinarith
  have hAB : B.AB P.k P.r ≤ A := by
    unfold B.AB
    rw [← hx]
    have : ((P.k : ℝ) + P.r) * x ≤ n * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    rw [← hx, ← hn]
    nlinarith
  have hint := (integrable_weight_normSq hXi p.T.base H A hCC hAB hT).indicator
    (Formalism.FourierDecayAlt.P.B7.isOpen_good_set p.T.base).measurableSet
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have h8 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hint
  refine h8.congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Function.comp]
  rw [he c]
  exact (Ew_bigPt_eq_indicator p H c).symm

theorem integrable_density_nil : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) :=
  fun h => integrable_density_nil_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory.HatNF.EmptyWordL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColengthBoundPrimeTwo
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem family_cast_iff {V : Type} (P : ∀ s : ℕ, (Fin s → V) → Prop) {n s : ℕ} (h : n = s) (g : Fin s → V) :
    P n (fun i => g (Fin.cast h i)) ↔ P s g := by
  subst h; rfl

theorem colength_bound_at_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∀ (f : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H f vd → ∃ xs : (E →+* ℂ) → NNReal, (∀ τ, InPsi H τ → HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) (xs τ)) ∧ (open Classical in (X.v ((p : ℕ) : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) := by
  intro p _ hAV E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy f vd hTP
  classical
  obtain ⟨U⟩ := GlobalTheory.T.nonempty_uniformised_formal_chart_algebraic_point E H Dw l Xo c T io y Ch hy p X
  obtain ⟨τT, -, hty, hinj, hrt, -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
  set τO : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ) with hτO
  have heig := fun τ => (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty τ).1
  obtain ⟨n, w, vdi, hwn, hsum, he, hu, hb, hvd⟩ := hTP X.C X.v X.O X.ints τO hinj hrt
  choose t hvd using hvd
  choose s hs hst using fun (i : Fin n) (j : Fin (w i).n) => he i (t i j : 𝓞 E →+* X.O) (t i j).2
  have hp : ∀ τ, InPsi H τ → Dw.p = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_pos h).symm
  have hq : ∀ τ, ¬ InPsi H τ → Dw.q = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_neg h).symm
  have hact : actMap U.ι' U.act = fun a i => MvPowerSeries.map X.ι (Ch.actT a i) := funext U.act_eq
  have hnu : ¬ IsUnit ((p : U.T'.V)) := fun h => X.nonunit.out (by have h' := h.map U.ι'; rwa [map_natCast] at h')
  have key := fun i0 : Fin n => hAV U.T'.V hnu U.t.G U.P.D U.P.A U.P.U.toUnifPre _ U.F U.x U.chart (𝓞 E)
    U.t.act.toRingAct U.P.oD U.P.oA U.P.lin U.act U.acts X.C X.v X.O X.ints U.ι' U.ι'_local (w i0) (t i0) (vdi i0) (hvd i0) Dw.p Dw.q
    (fun j i k => X.ι (Ch.uvecT ⟨s i0 j, Fin.cast (hp _ (hs i0 j)) i⟩ k))
    (fun j => by
      rw [hact, hst i0 j]
      exact (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO (s i0 j)) g)
        (hp _ (hs i0 j)) (fun i k => X.ι (Ch.uvecT ⟨s i0 j, i⟩ k))).2 (heig (s i0 j)))
    (fun σ hσ => by
      obtain ⟨τ, hτ, rfl⟩ := hb i0 σ hσ
      rw [hact]
      exact ⟨_, (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) g)
        (hq _ hτ) (fun i k => X.ι (Ch.uvecT ⟨τ, i⟩ k))).2 (heig τ)⟩)
  choose xs hxs hle using key
  let σs : (Σ i : Fin n, Fin (w i).n) → (E →+* ℂ) := fun z => s z.1 z.2
  have hmem : ∀ i j, τO (s i j) ∈ Emb (O := X.O) (w i).e := fun i j => by rw [← hst i j]; exact (t i j).2
  have hsinj : Function.Injective σs := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : s i j = s i' j' := h
    obtain rfl : i = i' := (hu _ (hs i j)).unique (hmem i j) (by rw [h']; exact hmem i' j')
    have : j = j' := by
      apply (t i).injective
      apply Subtype.ext
      rw [hst i j, hst i j', h']
    rw [this]
  have hssurj : ∀ τ, InPsi H τ → ∃ z, σs z = τ := fun τ h => by
    obtain ⟨i, hi, -⟩ := hu τ h
    refine ⟨⟨i, (t i).symm ⟨τO τ, hi⟩⟩, hinj ?_⟩
    have := hst i ((t i).symm ⟨τO τ, hi⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  let xz : (Σ i : Fin n, Fin (w i).n) → NNReal := fun z => xs z.1 z.2
  refine ⟨Function.extend σs xz (fun _ => 1), ?_, ?_⟩
  · intro τ hτ
    obtain ⟨⟨i, j⟩, rfl⟩ := hssurj τ hτ
    rw [hsinj.extend_apply, ← U.law_eq]
    exact (family_cast_iff (fun _ g => HasAF X.v (U.F.mapF U.ι') g (xs i j))
        (hp _ (hs i j)) (fun i' k => X.ι (Ch.uvecT ⟨s i j, i'⟩ k))).1 (hxs i j)
  · have hprod : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), ((Function.extend σs xz (fun _ => 1) τ : NNReal) : ℝ) =
        ∏ z, (xz z : ℝ) := by
      symm
      refine Finset.prod_bij (fun z _ => σs z) (fun z _ => by simpa using hs z.1 z.2) (fun j _ j' _ h => hsinj h)
        (fun τ hτ => ?_) (fun j _ => by rw [hsinj.extend_apply])
      obtain ⟨j, hj⟩ := hssurj τ (by simpa using hτ)
      exact ⟨j, Finset.mem_univ _, hj⟩
    have h2 : algebraMap X.O X.C (p : X.O) = (p : X.C) := map_natCast _ _
    have hpp : p.Prime := Fact.out
    have hr0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
      have : X.v (p : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
      exact_mod_cast pos_iff_ne_zero.2 this
    have hr1 : (X.v (p : X.C) : ℝ) ≤ 1 := by
      have hle : X.v (p : X.C) ≤ 1 := by rw [← h2]; exact X.ints.map_le_one _
      exact_mod_cast hle
    have h1 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      rw [div_le_one (by linarith)]; linarith
    have hi : ∀ i, (X.v (p : X.C) : ℝ) ^ (((w i).n : ℝ) * Dw.q * (1 + vdi i / 2)) ≤ ∏ j, (xs i j : ℝ) := fun i => by
      have h3 := NNReal.coe_le_coe.2 (hle i)
      rw [h2, NNReal.coe_rpow, NNReal.coe_prod] at h3
      refine le_trans (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_) h3
      have : (0 : ℝ) ≤ ((w i).n : ℝ) * Dw.q := by positivity
      nlinarith
    have hexp : (f : ℝ) * Dw.q * (1 + vd / 2) = ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) := by
      have a1 : (f : ℝ) = ∑ i, ((w i).n : ℝ) := by rw [← hwn]; push_cast; rfl
      have a2 : ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) =
          Dw.q * (∑ i, ((w i).n : ℝ)) + Dw.q / 2 * ∑ i, ((w i).n : ℝ) * vdi i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [a2, hsum, ← a1]; ring
    have hfin : (X.v (p : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ z, (xz z : ℝ) := by
      rw [hexp, Real.rpow_sum_of_pos hr0, Fintype.prod_sigma]
      exact Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos hr0 _).le) fun i _ => hi i
    convert hfin using 1

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NeZeroOfIsLocPt
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.TopDensityBound

section aux

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_comp_sq_le (E : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (E.comp X)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact E.le_opNorm _

variable {P : M.Par}

theorem V_eq_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (h : ¬ 0 < TBB.Gp p γ) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dif_neg]
  exact fun h' => h h'.2

theorem RR_cons (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (hw : w ≠ [])
    {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR F (P.r + 1) w γ γ = ((∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
      Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e F) γ))‖ ^ 2 : ℝ) : ℂ) := by
  have : p.RR F (P.r + 1) w γ γ = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w γ γ := by
    simp [KB.Pl.RR, D.RRplace, hγ, hw]
  rw [this]
  unfold Top.topOf
  push_cast
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  simp only [TBB.TTp, KB.Pl.V]
  push_cast
  ring

theorem Ew_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) w γ =
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)) *
        (p.RR F (P.r + 1) w γ γ).re := by
  unfold TBB.Ew TBB.NP TBB.normC
  rw [Complex.re_ofReal_mul]
  simp

theorem ne_zero_of_isLocPt {r : ℕ} (c : Fin (r + 1) → ℂ) (h : D.IsLocPt (TBB.bigPt r c) (r + 1)) (l : Fin (r + 1)) :
    c l ≠ 0 := by
  have := h.1 (1, c l) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨l, rfl⟩)
  exact this.2

theorem wPt_bigPt (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) = ‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c) := by
  unfold Top.wPt TBB.Gp
  have h : D.ptMatN (TBB.bigPt P.r c) (P.r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Complex.normSq_eq_norm_sq]

end aux

theorem top_density_le : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬((∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = 0) ∧ ((∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) ∧ TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) = TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 ∧ |TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)| ≤ C * TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * (‖∏ l, c l‖ ^ 2 / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length * ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) := by
  intro Wp Wq _ _ _ _ _ _ P p w
  set K : Ix (Fin w.length) → ℝ := fun e => ∑ ρ : M.Ty P, |(Top.cW P p.l0 w e ρ).re| * ‖p.TP.E ρ‖ ^ 2 with hK
  have hK0 : ∀ e, 0 ≤ K e := fun e => Finset.sum_nonneg fun ρ _ => by positivity
  have hS0 : 0 ≤ ∑ e, K e := Finset.sum_nonneg fun e _ => hK0 e
  refine ⟨1 + ∑ e, K e, by linarith, fun H c => ⟨fun hn => ?_, fun hc hG => ?_⟩⟩
  · rw [Ew_eq]
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := fun h => hn ⟨ne_zero_of_isLocPt c hl, h⟩
      by_cases hw : w = []
      · subst hw
        rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.RR_top p H hl, V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self,
          Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
        simp
      · rw [RR_cons p H w hw hl]
        simp [V_eq_zero p _ _ hG, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_zero]
    · have : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) = 0 := by
        simp [KB.Pl.RR, D.RRplace, hl]
      rw [this]; simp
  · have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
    have hn : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) := by
      unfold TBB.TTp
      rw [Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt _ _ _ _ c hζ.le]
      exact Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _
    have hnil : TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) =
        TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
      rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p H hl, Real.mul_self_sqrt hn]
    refine ⟨hn, hnil, ?_⟩
    by_cases hw : w = []
    · subst hw
      rw [hnil, abs_of_nonneg (by positivity)]
      simp only [p.Θ.nil, List.length_nil, pow_zero, mul_one]
      rw [Finset.sum_const]
      have hcard : (Finset.univ : Finset (Ix (Fin 0))).card = 1 := by simp [Ix]
      rw [hcard, one_smul]
      have : 0 ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2 := by
        positivity
      rw [mul_assoc]
      exact le_mul_of_one_le_left this (le_add_of_nonneg_right hS0)
    · rw [Ew_eq, Real.mul_self_sqrt hn, RR_cons p H w hw hl, Complex.ofReal_re, abs_of_nonneg (by positivity),
        ← wPt_bigPt]
      set Wt := Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) with hWt
      have hW0 : 0 ≤ Wt := by rw [hWt, wPt_bigPt]; positivity
      have key : (∑ e : Ix (Fin w.length), ∑ ρ : M.Ty P,
          Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
            ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2) ≤
          (1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        set v := ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2 with hv
        have hv0 : 0 ≤ v := by positivity
        have hKe : K e ≤ 1 + ∑ e, K e := by
          have := Finset.single_le_sum (f := K) (fun e _ => hK0 e) (Finset.mem_univ e)
          linarith
        calc _ ≤ K e * Wt ^ w.length * v := by
              simp only [hK]
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_le_sum fun ρ _ => ?_
              have h1 : Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 ≤
                  Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re| := by
                unfold Top.dH
                rw [← hWt, Real.sq_sqrt']
                exact max_le (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
              have h2 := hsVec_comp_sq_le (p.TP.E ρ) (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))
              calc _ ≤ (Wt ^ w.length * |(Top.cW P p.l0 w e ρ).re|) * (‖p.TP.E ρ‖ ^ 2 * v) :=
                    mul_le_mul h1 h2 (by positivity) (by positivity)
                _ = _ := by ring
          _ ≤ _ := by gcongr
      calc _ ≤ TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) * ((1 + ∑ e, K e) * Wt ^ w.length *
            ∑ e : Ix (Fin w.length), ‖B.hsVec (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left key hn
        _ = _ := by ring

end GlobalTheory.TopDensityBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopForm
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopDensity

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem RR_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    ∃ x : ℝ, 0 ≤ x ∧ p.RR H (P.r + 1) w γ γ = (x : ℂ) := by
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · exact ⟨_, sq_nonneg _, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self _⟩
  · unfold Top.topOf
    simp_rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    exact ⟨_, Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun ρ _ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _), rfl⟩
  · exact ⟨0, le_rfl, by simp⟩
  · exact ⟨0, le_rfl, by simp⟩

theorem RR_top_zero (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt)
    (hv : ∀ F, p.V F γ = 0) : p.RR H (P.r + 1) w γ γ = 0 := by
  have hv' : ∀ F, D.vecV p.T.base p.ν' p.m₀ F γ = 0 := hv
  have h0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
    unfold B.hsInner B.hsVec
    have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) =>
        (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
      simp; rfl
    rw [this, inner_zero_right]
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv', h0]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv', ContinuousLinearMap.comp_zero, h0, mul_zero]
  · rfl
  · rfl

theorem V_bigPt_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hζ : Complex.normSq (c (Fin.last P.r)) ≤ TBB.TTp p) : p.V F (TBB.bigPt P.r c) = 0 := by
  show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
  unfold D.vecV
  rw [dif_neg]
  rintro ⟨-, hG⟩
  have := Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  exact absurd this (not_lt.2 hζ)

theorem nPt_eq_prod (P : M.Par) (c : Fin (P.r + 1) → ℂ) (hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))) :
    TBB.nPt P.k P.r (P.T * P.T') (TBB.bigPt P.r c) = ∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i) := by
  unfold TBB.nPt
  have e : D.ptGG (P.T * P.T') (TBB.bigPt P.r c) = Complex.normSq (c (Fin.last P.r)) - P.T * P.T' := by
    unfold D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  rw [e]
  unfold TBB.bigPt
  rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold KB.levW
  rw [add_comm 1 (i : ℕ)]
  split_ifs with h
  · have hi : i = Fin.last P.r := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hi
    unfold B2.zWeight
    rw [if_pos hζ]
  · rfl

theorem levW_nonneg (P : M.Par) (i : ℕ) (c : ℂ) : 0 ≤ KB.levW P i c := by
  unfold KB.levW B2.zWeight
  split_ifs with h1 h2
  · exact pow_nonneg (sub_nonneg.2 h2) _
  · exact le_rfl
  · exact zpow_nonneg (norm_nonneg _) _

theorem topDensity_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  intro Wp Wq _ _ _ _ _ _ P p H w c _
  obtain ⟨x, hx, hRR⟩ := RR_top_diag p H w (TBB.bigPt P.r c)
  refine ⟨?_, by rw [hRR, Complex.ofReal_im], by rw [hRR, Complex.ofReal_re]; exact hx⟩
  have hTT : TBB.TTp p = P.T * P.T' := by
    unfold TBB.TTp
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  by_cases hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))
  · have hn : TBB.normC (fun _ => 1) w = 1 := by
      unfold TBB.normC
      simp
    unfold TBB.Ew TBB.NP
    rw [hn, hTT, nPt_eq_prod P c hζ, div_one,
      Real.mul_self_sqrt (Finset.prod_nonneg fun i _ => levW_nonneg P _ _), Complex.re_ofReal_mul]
  · have h0 := RR_top_zero p H w (TBB.bigPt P.r c) fun F =>
      V_bigPt_zero p F c (by rw [hTT]; exact (not_le.1 hζ).le)
    unfold TBB.Ew TBB.NP
    rw [h0]
    simp

end GlobalTheory.TopDensity
end

