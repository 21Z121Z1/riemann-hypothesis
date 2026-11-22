import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyTraitU_of_kapF : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  intro κ hK V _ _ _ _ hcpl hfin D x G _ _ hG U w₀ hN y hy hvec σ hNz hMaps
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding V hcpl hfin
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := hK V hcpl hfin D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def LabTors {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (k : ℕ)
    (x : QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)) : Prop :=
  (∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ k = 1 → ∃ p, x p = y) ∧ (∀ p, x p ^ k = 1) ∧
    (∀ p p', x p = x p' ↔ QkPt.Equiv D (Kb R) p p') ∧
    (∀ p p' p'', QkAdd p p' p'' → x p'' = x p * x p') ∧
    ∀ p p' (z : (Kb R)ˣ), WeilQkIs D (Kb R) k p p' z ↔ WeilIs A.A A.L k (x p) (x p') (unitOn z)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem lamPts_comp {S : Scheme.{0}} {B T T' : Over S} [GrpObj B] (f : T' ⟶ T) (x y : T ⟶ B) (l : Fin 4) :
    f.left ≫ GlobalTheory.PolDeg.lamPts x y l = GlobalTheory.PolDeg.lamPts (f ≫ x) (f ≫ y) l := by
  fin_cases l <;> simp [GlobalTheory.PolDeg.lamPts, ← Over.comp_left, MonObj.comp_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ T.pr i) (snd D'.P.A D'.P.A ≫ T.pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst D.P.A D.P.A else 1) (snd D.P.A D.P.A ^ m j i₀) l := by
  have h1 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ T.pr i = if i = i₀ then fst D.P.A D.P.A else 1 := by
    rw [lift_fst_assoc, Category.assoc, T.inc_pr']
    split_ifs <;> simp
  have h2 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ T.pr j = snd D.P.A D.P.A ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, T.act_pr]
    have e : ∀ k, (snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then snd D.P.A D.P.A else 1 := fun k => by
      rw [Category.assoc, T.inc_pr']; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd D.P.A D.P.A ≫ T.inc i₀) (∏ k, T.pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ i : Fin r) (a : D.X) : T.xe (T.xi i₀ a) i = if i = i₀ then a else 0 := by
  simp [Tens.xi, Pi.single_apply]

theorem c_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℤ) (b : D.X) : D.c (n • b) = D.c b ^ n := by
  let φ : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (D.c x)) (fun a b => by
      show Additive.ofMul (D.c (a + b)) = Additive.ofMul (D.c a * D.c b)
      rw [D.c_add]; rfl)
  exact congrArg Additive.toMul (map_zsmul φ n b)

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : D.X) (a' b' : D'.X)
    (ha : ∀ i, T.xe a' i = if i = i₀ then a else 0) (hb : ∀ j, T.xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) ≫
        lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) := by
  have c0 : D.c 0 = 1 := by
    have := c_zsmul D 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, ha, T.inc_pr']
    split_ifs <;> simp [c0]
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, hb, c_zsmul, T.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then toUnit (TK R) ≫ D.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, T.inc_pr']; split_ifs <;> simp
    calc toUnit (TK R) ≫ D.c b ^ m i i₀ = (toUnit (TK R) ≫ D.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ ∏ k, T.pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) (∏ k, T.pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

end GlobalTheory.TensPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem totallyComplex_core : IsTotallyComplex p.T.Q.c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem goodOf_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp σ = ComplexEmbedding.conjugate σ := by
    ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [e]; exact goodOf_conj (c := c) σ

theorem nrmK_conj (σ : p.T.Q.c.F →+* ℂ) (x : VK p.fw i) :
    nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := by
  simp only [nrmK, normW, petW]
  rw [goodOf_conj']

theorem slopeMax_all_le (Cm : ℝ) (hG : GramAt p i) (hM : MeasAt p i Cm) :
    slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) ≤
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) + 2 * (Cm * unitE p) := by
  haveI := totallyComplex_core p
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  choose c hc0 hcB hcE using hM
  have hAll : latAll p.R.toRealDat i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) : Set (VK p.fw i))) := by
    unfold latAll; rw [h3]
  have hne : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
    intro h0
    apply hG.2.2.1
    refine le_bot_iff.1 ((latGood_le _ _ _).trans ((inf_le_left : latType p.R.toRealDat p.F.lv2 i ≤ latAll p.R.toRealDat i).trans ?_))
    change latAll p.R.toRealDat i ≤ ⊥
    rw [hAll, h0]
    simp
  have key := GlobalTheory.T.maxSlope_sq_fieldExtension_le_comparable_norms p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL) (nrmK p.fw i)
    (nrmR p.R.toRealDat i) ι (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) c (Cm * unitE p) hG.2.2.2.1 hG.1 (nrmK_conj p i) h2
    hG.2.2.2.2.1 hne (fun σ => ⟨hc0 σ, hcB σ⟩) (fun σ x => by
      obtain ⟨h, e⟩ := h1 x
      rw [e]
      exact hcE σ ⟨x, h⟩)
  rw [hAll]
  exact key

theorem unitE_le {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    unitE p ≤ L.sc.x ^ (A + 1) * L.sc.b := by
  rw [hW.unit]
  have hX : 10 ≤ L.sc.x := hH.big.2.1.trans hH.big.2.2.1
  have hX0 : 0 < L.sc.x := by linarith
  have hL0 : 0 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb : 0 ≤ L.sc.b := le_trans (by positivity) hH.room
  have hlog : Real.log L.sc.x ≤ L.sc.x - 1 := Real.log_le_sub_one_of_pos hX0
  have hlogpos : 0 < Real.log L.sc.x := Real.log_pos (by linarith)
  have hll : Real.log (Real.log L.sc.x) ≤ L.sc.x := by
    have := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L.sc.x) := by linarith [hH.big.2.2.2]
  have hmr : D.R.m ≤ D.R.r * D.R.nV := by
    have h1 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
    have h2 : 1 ≤ D.R.nV := by have := D.R.two_le_m; unfold Ranks.nV; omega
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hmr' : (D.R.m : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by exact_mod_cast hmr
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hfm : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hmr' hf
    have := mul_le_mul_of_nonneg_right this hL0
    linarith
  have hpoly := hH.poly.2.2
  have hfm0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.L := by positivity
  calc (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
        = ((D.R.f : ℝ) * D.R.m * L.sc.L) * (L.sc.b * Real.log (Real.log L.sc.x)) := by ring
    _ ≤ L.sc.x ^ A * (L.sc.b * L.sc.x) :=
        mul_le_mul (hfm.trans hpoly) (mul_le_mul_of_nonneg_left hll hb) (by positivity) (by positivity)
    _ = L.sc.x ^ (A + 1) * L.sc.b := by rw [Real.rpow_add_one hX0.ne']; ring

theorem le_rpow_of_add {X b A1 A Cm u s : ℝ} (hX : 10 ≤ X) (hb : 0 ≤ b) (hA1 : 0 ≤ A1) (hA : 0 ≤ A) (hCm : 0 ≤ Cm)
    (hu : u ≤ X ^ (A + 1) * b) (hs : s ≤ X ^ A1 * b + 2 * (Cm * u)) :
    s ≤ X ^ (A1 + (A + 1) + (⌈2 * Cm⌉₊ : ℝ)) * b := by
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ X ^ A1 := Real.one_le_rpow (by linarith) hA1
  have hQ : 1 ≤ X ^ (A + 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hK : 1 + 2 * Cm ≤ X ^ (⌈2 * Cm⌉₊ : ℝ) := by
    rw [Real.rpow_natCast]
    have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ X - 1 by linarith) ⌈2 * Cm⌉₊
    have h2 : 2 * Cm ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * Cm⌉₊ : ℝ) ≤ (⌈2 * Cm⌉₊ : ℝ) * (X - 1) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
    have h4 : (1 : ℝ) + (X - 1) = X := by ring
    rw [h4] at h1
    linarith
  rw [Real.rpow_add hX0, Real.rpow_add hX0]
  set P := X ^ A1
  set Q := X ^ (A + 1)
  set K := X ^ (⌈2 * Cm⌉₊ : ℝ)
  have e1 : P * b ≤ P * Q * b := by
    have : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hQ
    exact mul_le_mul_of_nonneg_right this hb
  have e2 : 2 * (Cm * u) ≤ 2 * Cm * (P * Q * b) := by
    have : u ≤ P * Q * b := hu.trans (by
      have : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hP
      exact mul_le_mul_of_nonneg_right this hb)
    nlinarith
  have e3 : P * Q * b * (1 + 2 * Cm) ≤ P * Q * b * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith

theorem lam : Hypotheses2 → Gram → Meas → abelian₂ := by
  intro hP hG hM
  have hc := GlobalTheory.T.slope_max_squared_bound hP hG
  have hH : HostN 1 := GlobalTheory.CovTop.Sizes.hostN 1
  have hW : WtN := GlobalTheory.T.weight_bound_holds
  refine Closed.imp ((((hc.and hM).and hH).and hG).and hW) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨⟨⟨⟨A1, hA1, hc⟩, ⟨Cm, hCm, hm⟩⟩, ⟨Ah, hAh, hh⟩⟩, ⟨Cg, -, hg⟩⟩, ⟨Cw, -, hw⟩⟩ := h
  refine ⟨A1 + (Ah + 1) + (⌈2 * Cm⌉₊ : ℝ), by have := Nat.cast_nonneg (α := ℝ) ⌈2 * Cm⌉₊; linarith, ?_⟩
  obtain ⟨x0, H⟩ := (((hc.and hm).and hh).and hg).and hw
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := H x hx hle ι p hp
  have hH1 := c i
  have hX : 10 ≤ (Fm.L x ι).sc.x := hH1.big.2.1.trans hH1.big.2.2.1
  have hb : 0 ≤ (Fm.L x ι).sc.b := le_trans (by positivity) hH1.room
  exact le_rpow_of_add hX hb hA1 (by linarith [hH1.poly.1]) hCm (unitE_le p i hH1 (e i))
    ((slopeMax_all_le p i Cm (d i) (b i)).trans (by linarith [a i]))

end GlobalTheory.CovTop.LamAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisFractionFieldIndependentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_fraction_field_independent : ∀ {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {R : Type} [CommRing R] [IsDomain R]
    {L : Type} [Field L] [Algebra R L] (j : FractionRing R →+* L)
    (hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = algebraMap R L x) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module L V] (β : (Fin n → R) →ₛₗ[algebraMap R L] V)
    (hβ : LinearIndependent L (fun k ↦ β (Pi.single k 1)) ∧ Submodule.span L (Set.range fun k ↦ β (Pi.single k 1)) = ⊤)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (T : orderC c → Module.End L V)
    (hT : ∀ a x, β (ρ a x) = T a (β x)) (N : Submodule R (Fin n → R)) {I : Type} [Fintype I]
    (σ : I → E →+* FractionRing R)
    (h : Submodule.span L (β '' (N : Set (Fin n → R))) = ⨆ i, ⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ i a))),
   N.baseChange (FractionRing R) = ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (σ i) := by
  first | exact @GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK | exact GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK | (intros; apply GlobalTheory.EigDescentFrac.baseChange_eq_iSup_eigK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEigenvectorHeightMatrix
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

theorem GlobalTheory.CompHt.eigtau_sum_mem_latT_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (δ : ℂ_[p]), δ ≠ 0 → ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H),
      (∀ w ∈ Q.eigV (embInt c Q.integers τ.1), (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)) →
      ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers τ.1) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q τ.1) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖δ⁻¹ * a i‖ ≤ 1) := by
  intro E _ _ _ H p _ δ hδ l c _ Q τ hyp n xx g hx hb a
  letI := H.starRing
  set s := ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) with hs
  have hsV : s ∈ Q.eigV (embInt c Q.integers τ.1) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  have h1 := hyp (δ⁻¹ • s) (Submodule.smul_mem _ _ hsV)
  rw [smul_smul, mul_inv_cancel₀ hδ, one_smul] at h1
  rw [← h1, hs, Finset.smul_sum]
  simp_rw [smul_smul]
  rw [hb.sum_mem_iff]
  simp_rw [mem_range_iff_norm_le]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassModStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.least_vector_unique_in_class_mod : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  first | exact @GlobalTheory.Poinc.LeastVec.least_lt_add_smul | exact GlobalTheory.Poinc.LeastVec.least_lt_add_smul | (intros; apply GlobalTheory.Poinc.LeastVec.least_lt_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureCrtCombineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_crt_combine : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  first | exact @GlobalTheory.RealMult.Obj.Level.comb | exact GlobalTheory.RealMult.Obj.Level.comb | (intros; apply GlobalTheory.RealMult.Obj.Level.comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePowerSplitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_power_split : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  first | exact @GlobalTheory.RealMult.Obj.Level.exists_pow_levels | exact GlobalTheory.RealMult.Obj.Level.exists_pow_levels | (intros; apply GlobalTheory.RealMult.Obj.Level.exists_pow_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_base_change_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  first | exact @GlobalTheory.RealMult.Obj.lieBaseChange_equiv | exact GlobalTheory.RealMult.Obj.lieBaseChange_equiv | (intros; apply GlobalTheory.RealMult.Obj.lieBaseChange_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFreeRankDegreeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_free_rank_degree : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (R : Type) [CommRing R] [IsLocalRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Free R X.Lie ∧ Module.Finite R X.Lie ∧ Module.finrank R X.Lie = Module.finrank ℚ F := by
  first | exact @GlobalTheory.Lie.free_finrank_of_isLocalRing | exact GlobalTheory.Lie.free_finrank_of_isLocalRing | (intros; apply GlobalTheory.Lie.free_finrank_of_isLocalRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImagePolynomialEndomorphismStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_polynomial_endomorphism : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (α : A ⟶ A) [IsMonHom α]
    (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)), (∀ z, u.ex (D z) = u.ex z ≫ α) →
    ∀ (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ), IsLieImage h v → u.IsDiff w v → D w = c • w →
    ∀ Q : Polynomial ℂ, ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  first | exact @GlobalTheory.LieImagePoly.exists_isLieImage_aeval | exact GlobalTheory.LieImagePoly.exists_isLieImage_aeval | (intros; apply GlobalTheory.LieImagePoly.exists_isLieImage_aeval <;> assumption)
end

