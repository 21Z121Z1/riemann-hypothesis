import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstTwoPointsPowerSeriesZeroOfVanishFirstAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffDpolyNEqDerivAt0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitMatrixGauge
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0117
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
section
open AlgebraicGeometry CategoryTheory
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.CompletionPoint

theorem exists_intFr_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  intro E _ _ _ H Dw l Xo c hpq hg Z K _ _ _ y hy w 𝔭 hv
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  obtain ⟨O, _, β, Y, -, hPI, hbase⟩ := GlobalTheory.Frames.modelAtSt_of_good hP hN E H Dw l Xo c hpq hg w
  obtain ⟨T, k, hk, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K 𝔭
  have ho : OverLa w T.V (k.comp (algebraMap c.F K)) 1 :=
    ⟨Nat.one_pos, fun a => by rw [← hv a]; exact hk.2 _⟩
  obtain ⟨b, hb⟩ := hbase T _ 1 ho
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp (algebraMap c.F K)).toAlgebra
  have hz : ptF y ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F K) := Limits.pullback.lift_snd _ _ _
  have hs : (spMap k ≫ ptF y) ≫ Limits.pullback.snd _ _ = spMap (k.comp (algebraMap c.F K)) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ ptF y) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y', t, hbor⟩ := intFr_of_model hIF T (k.comp (algebraMap c.F K)) Y hPI b hb y₀
  refine ⟨T, k.comp (algebraMap c.F K), y', ho, hfin, fun q => ?_⟩
  have h1 : y'.1.x = y₀.x := hbor.1
  have h2 : ptF y'.1 = spMap k ≫ ptF y := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst _ _ _).trans (h1.trans h0)
    · exact (Limits.pullback.lift_snd _ _ _).trans hs.symm
  rw [h2]
  exact hy (spMap k q)

end GlobalTheory.CompletionPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValue
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ColApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem map_polyT {T : CDVR} {C : Type} [Field C] (φ : T.Fr →+* C) (cx : Lt1 Dw → ℕ) {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) :
    MvPolynomial.map φ (polyT B cx) = MvPolynomial.aeval (fun ℓ : Let cx => ∑ j,
      MvPolynomial.C (φ (algebraMap T.V T.Fr (B ℓ.1.1.1 ℓ.1.2 j))) *
        (MvPolynomial.X ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩ : MvPolynomial (LtN Dw n) C)) (polyH C cx) := by
  classical
  unfold polyT polyP polyH
  rw [map_prod, map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero, map_one])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) _ (fun f => by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, GlobalTheory.FGDepth.detPow, map_pow, map_pow, RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext a b : 2
  simp [GlobalTheory.CombMinor.cMat]

theorem exists_cols {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} {cx : Lt1 Dw → ℕ} {n : ℕ}
    {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V} (hB : IsCols c T io p cx B) (N : ℕ) :
    ∃ x : Col cx → Fin n → 𝓞 E,
      (∀ b j, ∃ z : T.V, io (embK c b.1.1.1 (x b j)) = algebraMap T.V T.Fr (B b.1.1 b.2 j + (p : T.V) ^ N * z)) ∧
      ∀ b b', ∑ j, H.bar (x b j) * x b' j ∈ Ideal.span {(p : 𝓞 E) ^ N} := by
  obtain ⟨blk, hb⟩ := hB
  choose x h0 h1 h2 using fun f => (hb f).2.2 N
  refine ⟨fun b => x b.1 b.2, fun b j => h1 b.1 b.2 j, ?_⟩
  rintro ⟨f, b⟩ ⟨f', b'⟩
  by_cases hf : f = f'
  · subst hf
    simpa only [mul_comm] using h2 f b' b
  · rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    intro j _
    dsimp only
    by_cases hj : j ∈ Set.range fun j => blk ⟨f, j⟩
    · rw [h0 f' b' j, mul_zero]
      rintro ⟨j2, e2⟩
      obtain ⟨j1, e1⟩ := hj
      exact hf (congrArg Sigma.fst (blk.injective (e1.trans e2.symm)))
    · rw [h0 f b j hj, map_zero, zero_mul]

theorem isIntV_ringHom {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (φ : 𝓞 E →+* X.C) (a : 𝓞 E) :
    IsIntV (vX_vp X) (φ a) := by
  rw [isIntV_iff, ← X.ints.isIntegral_iff_v_le_one]
  exact (map_isIntegral_int φ (Algebra.IsIntegral.isIntegral a)).tower_top

theorem le_v_pow_mul {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (N : ℕ) {z : X.C}
    (hz : IsIntV (vX_vp X) z) : (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * z) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p]
  refine le_add_of_le_of_nonneg (le_of_eq ?_) hz
  simp

theorem lin_col {C : Type} [Field C] {d m : ℕ} {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)]
    (e : κ ≃ Fin m) (u : ∀ b, ι b → Fin d → C) (q : Fin m) :
    lin (fun ℓ : Σ b, ι b => u ℓ.1 ℓ.2) (fun ℓ => if e ℓ.1 = q then 1 else 0) =
      fun i => ∑ a, u (e.symm q) a i • (MvPowerSeries.X ⟨e.symm q, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
  funext i
  unfold lin
  rw [Fintype.sum_sigma, Finset.sum_eq_single (e.symm q)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    have hq : e b ≠ q := fun h => hb (by rw [← h]; simp)
    simp [hq]
  · simp

theorem exists_germ_cols : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k g hg
  classical
  letI := io.toAlgebra
  obtain ⟨BT, -, -, -, -, -, -, e7⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := e7 X.C
  have hc := (h3 _).2 h4
  let eC := Fintype.equivFin (Col cx)
  let σ : Col cx → 𝓞 E →+* X.C := fun b => X.ιF.comp (io.comp (embK c b.1.1.1))
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct X.C BT a).mulVec (lieVec Ch X ℓ) =
      X.ιF (io (embK c ℓ.1 a)) • lieVec Ch X ℓ := by
    intro a ℓ
    funext i
    have h := congrArg X.ιF (congrFun (GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ℓ) i)
    have hu : ∀ i, lieVec Ch X ℓ i = X.ιF (Ch.ch.uvec ℓ i) := fun i =>
      congrArg X.ιF (Ch.gen.1.2.2.2.2.2.2 ℓ i).symm
    simp only [Matrix.mulVec, dotProduct, dAct, h2, hu, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, MvPowerSeries.coeff_map, map_sum, map_mul, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    exact h
  obtain ⟨K, hK⟩ := exists_germ_close (v := vX_vp X) BT (G := lawX Ch X) h1.symm (fgl Ch X).F_int
    (fun ℓ : Let cx => eC ℓ.1) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun b a => σ (eC.symm b) a)
    (fun a ℓ => by rw [eC.symm_apply_apply]; exact heig a _) (isIntV_jX X) hc H.w0
    (fun ℓ i => isIntV_jX X _) (fun b a => isIntV_ringHom X _ a)
    (fun x => (GlobalTheory.exists_integral_unit_matrix_gauge _ _ _ _ BT _ hc H.w0 _ n x).imp fun _ h => h.2)
    (polyH X.C cx) k g hg
  obtain ⟨N', hN'⟩ := exists_nat_ge ((N : ℝ) + K)
  obtain ⟨x, hx1, hx2⟩ := exists_cols hB N'
  let β : Col cx → Fin n → X.C := fun b j => jX X (B b.1.1 b.2 j)
  obtain ⟨f, hf, hv⟩ := hK N' (fun b => x (eC.symm b)) (fun b => β (eC.symm b)) (fun b j => isIntV_jX X _)
    (fun b j => by
      obtain ⟨z, hz⟩ := hx1 (eC.symm b) j
      have : β (eC.symm b) j - σ (eC.symm b) (x (eC.symm b) j) = (p : X.C) ^ N' * jX X (-z) := by
        show _ - X.ιF (io (embK c _ _)) = _
        rw [hz]
        show jX X _ - jX X _ = _
        simp
      rw [this]
      exact le_v_pow_mul X N' (isIntV_jX X _))
    (fun b b' => by
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (hx2 (eC.symm b) (eC.symm b'))
      have : σ (eC.symm b') (H.w0 * ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j) =
          (p : X.C) ^ N' * σ (eC.symm b') (H.w0 * r) := by
        rw [show ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j = _ from hr, mul_left_comm, map_mul, map_pow,
          map_natCast]
      rw [this]
      exact le_v_pow_mul X N' (isIntV_ringHom X _ _))
  have cX : ∀ q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch), MvPowerSeries.constantCoeff
      (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 0 := fun q => by simp
  have hE : MvPowerSeries.HasSubst (expH Ch X cx) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun q =>
    nc_exPt (fgl Ch X) (fun i => by simp) q.2
  refine ⟨MvPowerSeries.subst (fun q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch) =>
    (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)) f,
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _ hf
      (fun q α => by rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntV]) cX, ?_⟩
  refine le_trans (WithTop.coe_le_coe.2 (by linarith)) (hv.trans (le_of_eq ?_))
  congr 2
  · have hA := GlobalTheory.ExpCoord.constantCoeff_dpolyN_eq_derivAt0 X.C (vX_vp X) _ (lawX Ch X) (fgl Ch X) (fun _ => rfl) n (LtN Dw n) (Let cx)
      (fun ℓ => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (fun ℓ => β ℓ.1)
      (fun ℓ j => ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun _ _ => rfl)
      (fun _ _ => rfl) (polyH X.C cx)
    unfold nabX nabValN
    rw [map_polyT]
    simp only [eC.symm_apply_apply, FB.hL, h2]
    exact (hA _).symm
  · rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero cX) hE]
    congr 2
    funext q
    rw [MvPowerSeries.subst_X hE]
    unfold colExp
    rw [lin_col eC (fun b : Col cx => frame Ch X b.1.1)]
    rfl

end GlobalTheory.ColApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValue
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColumnGerm

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.IsoTriv

theorem mvIsInt_pow {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {σ : Type} {g : MvPowerSeries σ C}
    (hg : MvIsInt v g) (k : ℕ) : MvIsInt v (g ^ k) := by
  classical
  induction k with
  | zero =>
    intro α
    unfold IsIntV
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih => rw [pow_succ]; exact GlobalTheory.DepthNonneg.mvIsInt_mul ih hg

theorem exists_nabX_eq (hN : NabSt) (hI : InclSt) (hR : RetrSt) (hU : UnitSt) (hF : FrameSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
    {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (hB : IsCols c T io p cx B) (k : ℕ) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)
    (hf : MvIsInt (vX_vp X) f) :
    ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) f) := by
  obtain ⟨ψ, ψ0, -, ψe, ψU⟩ := hI E H Dw l Xo c hs T io y Ch p X cx n B hB
  obtain ⟨ρ, ρ0, ρi, ρe⟩ := hR E H Dw l Xo c hs T io y Ch p X cx n B hB
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero ψ0
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero ρ0
  have e0 : ∀ q, constantCoeff (expH Ch X cx q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have c0 : ∀ q, constantCoeff (colPt Ch X cx B q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have he : HasSubst (expH Ch X cx) := hasSubst_of_constantCoeff_zero e0
  have hc : HasSubst (colPt Ch X cx B) := hasSubst_of_constantCoeff_zero c0
  have fr1 : constantCoeff (frameX Ch X n) = 1 := by
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    exact (hF X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).1
  have U1 : constantCoeff (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 1 := by
    have h := constantCoeff_subst_eq_zero hψ ψ0 (f := frameX Ch X n - 1) (by rw [map_sub, fr1, map_one, sub_self])
    rw [← coe_substAlgHom hψ, map_sub, map_one, map_sub, map_one, sub_eq_zero, coe_substAlgHom] at h
    exact h
  obtain ⟨U', U'i, hU'⟩ := (hU X.C (vX_vp X) _).2.2.2.2.2 _ ψU U1
  refine ⟨subst ρ (f * U' ^ k), ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _
    (GlobalTheory.DepthNonneg.mvIsInt_mul hf (mvIsInt_pow U'i k)) ρi ρ0, ?_⟩
  rw [hN E H Dw l Xo c T io y Ch p X cx n B k]
  congr 1
  have h1 : subst (colPt Ch X cx B) (subst ρ (f * U' ^ k) : PS X.C n (chD Ch.ch)) =
      subst (expH Ch X cx) (f * U' ^ k) := by
    rw [subst_comp_subst_apply hρ hc, funext ρe]
  have h2 : subst (colPt Ch X cx B) (frameX Ch X n) = subst (expH Ch X cx)
      (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) := by
    rw [subst_comp_subst_apply hψ he, funext ψe]
  rw [subst_mul hc, subst_pow hc, h1, h2, ← subst_pow he, ← subst_mul he, mul_assoc, ← mul_pow, mul_comm U', hU',
    one_pow, mul_one]

end GlobalTheory.ColumnGerm

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColumnGerm

theorem exists_germ_on_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k f hf
  have hadd := GlobalTheory.T.logarithm_sum_integral_additive
  have hact := GlobalTheory.T.action_linear_logCoordinates_integral
  have hunit := GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof
  have hcont := GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof
  have hbi := GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear hadd hact
  have hfr := GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit hact hunit
  have hfin := GlobalTheory.T.gaugeHermitianCombination_of_steps hadd hact hunit hbi
  have hla := GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox GlobalTheory.T.primeIdempotentApproximationsDVR_proof
  have hlp := GlobalTheory.T.limitActionIntegralPoint_of_steps hadd hact hcont
  have hlf := GlobalTheory.T.limitIsotropicFrameIntegral_of_steps hadd hact hunit hbi hfr hfin hcont
  obtain ⟨g, hg, h⟩ := exists_nabX_eq (GlobalTheory.T.nablaOperatorFrameSeries_of_steps GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof hfr) (GlobalTheory.T.columnInclusionIntegral_of_limitSteps hla hlp hlf)
    (GlobalTheory.T.columnInclusionRetraction_of_limitSteps hla hlp GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof) hunit hfr (fun _ => rfl) Ch X cx B hB k f hf
  refine ⟨g, hg, ?_⟩
  rw [h, sub_self, AddValuation.map_zero]
  exact le_top

end GlobalTheory.ColumnGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  first | exact @GlobalTheory.KollarApp.isolatedNonKlt_smooth | exact GlobalTheory.KollarApp.isolatedNonKlt_smooth | (intros; apply GlobalTheory.KollarApp.isolatedNonKlt_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasisStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  first | exact @GlobalTheory.TanBasis.exists_point_tanBasis | exact GlobalTheory.TanBasis.exists_point_tanBasis | (intros; apply GlobalTheory.TanBasis.exists_point_tanBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CombTw

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem wt_diff_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) :
    wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m = wtOf Dw (parWt Dw (-w₀)) 0 + m • (-wtOf Dw 0 1) := by
  ext x
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.fst_neg, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply]
    simp only [wtOf, parWt, Pi.zero_apply, Pi.neg_apply, Pi.add_apply, nsmul_eq_mul]
    split_ifs <;> ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_neg]
    simp only [wtOf, nsmul_eq_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exists_mul_inv_pow {Z : Comp Xo c} {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (m : ℕ) :
    ∃ z : TwSec U x Z (G₀ + m • (-G₁)), z.lo = s.lo - (m : ℝ) • t.hi ∧ z.hi = s.hi - (m : ℝ) • t.lo := by
  induction m with
  | zero => exact ⟨s.copy (by simp), by simp [TwSec.copy], by simp [TwSec.copy]⟩
  | succ n ih =>
    obtain ⟨z, hlo, hhi⟩ := ih
    refine ⟨(z.mul t.symm).copy (by rw [succ_nsmul, add_assoc]), ?_, ?_⟩
    · show z.lo + -t.hi = _
      rw [hlo]; push_cast; rw [add_smul, one_smul]; abel
    · show z.hi + -t.lo = _
      rw [hhi]; push_cast; rw [add_smul, one_smul]; abel

theorem exists_twSec_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (B : Finset ℕ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (k : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : TwSec U x Z (wtOf Dw (parWt Dw (-w₀)) 0)) (t : TwSec U x Z (wtOf Dw 0 1)), s.hi = s.lo → IntOff B s.lo → IntOff B t.hi → (∀ w, t.hi w - t.lo w ≤ k w) → ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m), IntOff B z.lo ∧ ∀ w, z.hi w - z.lo w ≤ m * k w := by
  intro E _ _ _ H Dw l Xo c r U _ x B Z u w₀ m k s t hs hslo hthi hk
  obtain ⟨z, hlo, hhi⟩ := exists_mul_inv_pow s t m
  refine ⟨z.copy (wt_diff_eq Dw u w₀ m).symm, ?_, ?_⟩
  · show IntOff B z.lo
    rw [hlo]
    intro w hw
    obtain ⟨a, ha⟩ := hslo w hw
    obtain ⟨b, hb⟩ := hthi w hw
    exact ⟨a - m * b, by simp [ha, hb]⟩
  · intro w
    show z.hi w - z.lo w ≤ _
    rw [hhi, hlo]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hs]
    have := hk w
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

end GlobalTheory.CombTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  first | exact @GlobalTheory.nef_big_of_cls_eq_smul_add_smul | exact GlobalTheory.nef_big_of_cls_eq_smul_add_smul | (intros; apply GlobalTheory.nef_big_of_cls_eq_smul_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihilaStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExists.polForm_exists | exact GlobalTheory.PolExists.polForm_exists | (intros; apply GlobalTheory.PolExists.polForm_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_of_isGrpPullback : ∀ {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (b : OAct O G) {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G f φ → ∃ a : OAct O G', ∀ z, (a.act z).left ≫ φ = φ ≫ (b.act z).left := by
  first | exact @GlobalTheory.OActPull.exists_oAct_of_isGrpPullback | exact GlobalTheory.OActPull.exists_oAct_of_isGrpPullback | (intros; apply GlobalTheory.OActPull.exists_oAct_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallBoundTupleStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.CoefSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt | exact GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt <;> assumption)
end

