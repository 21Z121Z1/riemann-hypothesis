import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartFormalBiextensionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslates
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPullback

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (hz : r z ∈ V)
    (a : Γ(X, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  have key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz =
      r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res pullU
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom (a : Γ(X, U))) key

private theorem exists_isGen_linComb_val_eq_of_eq {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val t' r z J = val t r z J := by
  subst hφ
  exact ⟨t, ht, fun _ _ _ _ => rfl⟩

theorem whiskerRight_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  unfold translPt
  rw [← Category.assoc, comp_lift]
  simp

theorem translT_whiskerRight {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  ext <;> simp [translT, whiskerRight_translPt]

theorem negT_whiskerRight {T T' : Over S} (h : T' ⟶ T) :
    negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  ext <;> simp [negT]

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j : Fin n,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  have e : ∀ j : Fin n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J =
      val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm
  rw [Finset.prod_congr rfl fun j _ => e j]
  unfold powGen val
  dsimp only
  erw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact gm_res_eq_gm _ _ _ (hJ.mem _ r) _

theorem val_symGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  rw [val_mul hJ, val_mul hJ, val_inv]
  have e1 := val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r
  have e2 := val_pull hJ θ.φ (translT A θ.pt⁻¹).left r
  have e3 := val_pull hJ θ.φ (negT A T).left r
  have e4 := val_pull hJ ν (translT A θ.pt⁻¹).left r
  rw [e1, e2, e3, e4]

theorem exists_thetaGrp_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  intro S A _ _ L hL k T T' h θ
  have hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) =
      ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left] := by
    funext b
    fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, whiskerRight_snd]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Over.comp_left, whiskerRight_translPt]
  obtain ⟨φ', gφ', vφ'⟩ :=
    exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)
  have vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val φ' r z J = val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (h ▷ A).left) z J :=
    fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)
  have hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left) :=
    corr_of_val hL fun y J _ => vφ' _ _ y J
  have hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]
  have hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹ := GrpObj.comp_inv h θ.pt
  refine ⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩
  · intro n x hs
    obtain ⟨hpt, hpw, nu, gnu, hsym⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · show h ≫ θ.pt = h ≫ x
      rw [hpt]
    · refine corr_of_val hL fun y J hJ => ?_
      have hθ1 := val_corr hJ hpw (h ▷ A).left
      rw [val_one, val_powGen _ _ _ hJ] at hθ1
      rw [val_one, val_powGen _ _ _ hJ, ← hθ1]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only
      rw [vθ _ _ _ _ hJ]
      have e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]
      rw [e]
    · have hφn : (fun b => (h ▷ A).left ≫
            (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) =
          ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] := by
        funext b
        fin_cases b
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [← Over.comp_left, whiskerRight_snd]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← Over.comp_left, whiskerRight_snd_assoc]
      obtain ⟨nu', gnu', vnu'⟩ :=
        exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)
      have vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
          val nu' r z J = val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J :=
        fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)
      refine ⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩
      have hθ2 := val_corr hJ hsym (h ▷ A).left
      rw [val_one, val_symGen _ _ _ hJ] at hθ2
      rw [val_one]
      refine (val_symGen _ _ _ hJ).trans ?_
      rw [← hθ2]
      dsimp only
      rw [vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]
      have e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]
      have e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]
      rw [e1, e3, Category.id_comp]
  · intro s t s' t' hact hs ht
    unfold IsActOf at hact ⊢
    exact GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _
      (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht

end GlobalTheory.ThetaPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicValueBaseChange

set_option maxHeartbeats 1000000 in

theorem sum_map_of_harmA (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [CommRing S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hstar, hnabC⟩ := hnab
  obtain ⟨C, hex, hval⟩ := hnabC S y
  choose f hf using fun b => hex k (F b)
  rcases y' with ⟨x1, xo, u1, tn, eg, bs, s1, gn⟩
  obtain ⟨hx, hu, -⟩ := hm
  subst hx
  have hu' : u1 = fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i := by
    funext τ i
    exact hu τ i
  subst hu'
  have hh' : h = ptBC ψ.toRingHom y.x := by
    apply Over.OverMorphism.ext
    rw [hh]
    rfl
  subst hh'
  obtain ⟨B', x', e', -, hG, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    GlobalTheory.T.rawChart_formalBiextension_baseChange E H Dw l Xo c S S' ψ y.x y.u (Formalism.MainNotions.ModuliIntegralCharts.H1.ChartAt.toRaw C)
  let C' : ChartAt Xo c ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') :=
    { d := C.d, B := B', uvec := fun ℓ j => ψ (C.uvec ℓ j), x := x', e := e', wP := C.wP, h := MvPowerSeries.map ψ.toRingHom C.h, chart := ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩, frame := ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, prim := C.prim, gauge := hga, rig0 := hrig }
  have hf' : ∀ b, IsGerm ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') C'.d C'.x C'.B.A.act C'.e C'.wP k (F' b)
      (MvPowerSeries.map ψ.toRingHom (f b)) := by
    intro b
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.isGerm_iff_raw]
    exact hgerm k (F b) (F' b) (f b) (hF' b)
      ((Formalism.MainNotions.ModuliIntegralCharts.H1.isGerm_iff_raw y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)).1 (hf b))
  obtain ⟨C2, hex2, hval2⟩ := hnabC S' ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S')
  choose f2 hf2 using fun b => hex2 k (F' b)
  have hCI := hC E H Dw l Xo c hstar S' ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') C' C2 k n F' (fun b => MvPowerSeries.map ψ.toRingHom (f b)) f2
    hf' hf2 a P hP
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal at hCI
  have e1 : ∀ b α, nab y (k : ℤ) (F b) α =
      C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial α 1) :=
    fun b α => hval k (F b) (f b) (hf b) α
  have e2 : ∀ b α, nab ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') (k : ℤ) (F' b) α =
      C2.B.nabVal S' C2.h H.w0 k (f2 b) C2.uvec (MvPolynomial.monomial α 1) :=
    fun b α => hval2 k (F' b) (f2 b) (hf2 b) α
  simp only [e1, e2]
  rw [← hCI, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_prod, AlgHom.commutes]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hmap := nabMap_holds S S' ψ.toRingHom C.d (𝓞 E) C.B B' hG hA C.h C.gauge H.w0 k (f b) (Lt1 Dw)
    C.uvec (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hmap
  exact hmap.symm

end GlobalTheory.HarmonicValueBaseChange

namespace GlobalTheory

theorem harmonicValue_baseChange : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S S' _ _ _ _ ψ y y' hm h hh a n P hP N F F' hF'
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  let _ : Algebra ℚ S' := ((algebraMap c.F S').comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨D, hD0, hDi⟩ := exists_integral_multiples ℤ ℚ (P.support.image fun m => P.coeff m)
  have hsupp : (D • P).support = P.support := MvPolynomial.support_smul_eq hD0 P
  have hQ1 : D • P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    unfold HHa at hP ⊢
    simp only [Set.mem_ofPred_eq] at hP ⊢
    obtain ⟨hker, hrow, hdeg⟩ := hP
    refine ⟨zsmul_mem hker D, fun σ i i' hi t => ?_, fun m hm => hdeg m (hsupp ▸ hm)⟩
    rw [map_zsmul, hrow σ i i' hi t]
  have hQ : D • P ∈ harmA c a n := by
    unfold harmA HaO
    simp only [Set.mem_ofPred_eq]
    refine ⟨hQ1, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul]
    by_cases hmem : m ∈ P.support
    · exact hDi _ (Finset.mem_image_of_mem _ hmem)
    · have h0 : P.coeff m = 0 := by simpa using hmem
      rw [h0, smul_zero]
      exact zero_mem _
  have key := HarmonicValueBaseChange.sum_map_of_harmA hC nab hnab ψ y y' hm h hh a n (D • P) hQ
    ((N : ℤ) ^ 2) (N ^ 2) (by push_cast; ring) F F' hF'
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, map_zsmul, smul_mul_assoc, ← Finset.smul_sum] at key
  simp only [zsmul_eq_mul] at key
  have hu : IsUnit (D : S') := by
    rw [← map_intCast (algebraMap c.F S') D]
    exact (IsUnit.mk0 _ (Int.cast_ne_zero.2 hD0)).map _
  exact hu.mul_left_cancel key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  first | exact @GlobalTheory.modN_sq_iff_exists_genLat_sum | exact GlobalTheory.modN_sq_iff_exists_genLat_sum | (intros; apply GlobalTheory.modN_sq_iff_exists_genLat_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPoints

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem section_ext [IsReduced S] {G : Over S} [IsSeparated G.hom] (f g : 𝟙_ (Over S) ⟶ G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      toUnit (Over.mk x) ≫ f = toUnit (Over.mk x) ≫ g) : f = g := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  refine Over.OverMorphism.ext (hom_ext_of_geometricPoints_dense G.hom f.left g.left
    ((Over.w f).trans (Over.w g).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
  have e : (toUnit (Over.mk (Y := Sp k) (X := S) x)).left = x :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (Y := Sp k) (X := S) x)))
  have := congrArg CommaMorphism.left (h k x)
  simp only [Over.comp_left] at this
  rw [e] at this
  exact this

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 := o.eta_ker 0 (Submodule.zero_mem _)

theorem eta_nsmul (o : Obj D l b s) (n : ℕ) (a : D.La) : o.eta (n • a) = o.eta a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem natCast_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

theorem eta_pow (o : Obj D l b s) (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [← eta_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact o.eta_ker _ (Submodule.smul_mem_smul (natCast_mem l) Submodule.mem_top)

theorem eta_smul [IsReduced S] (o : Obj D l b s) (c : 𝓞 E) (a : D.La) :
    o.eta (c • a) = o.eta a ≫ o.t.act.act c := by
  have := o.proper
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have key : ∀ a : D.La, o.eta a = o.eta (v • a) := fun a => by
    conv_lhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, o.eta_add,
      o.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
  refine section_ext _ _ fun k _ _ x => ?_
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (by
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  rw [key a, key (c • a), ← Category.assoc, hI _ (Submodule.smul_mem_smul hv Submodule.mem_top),
    hI _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v c a, I.lin]

end LevelPoints

theorem moduli_univ_eta_killed :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (a : Dw.La), (∀ b ∈ l.Mb, Xo.univ.eta a ≫ Xo.univ.t.act.act b = 1) ∧ (∀ b : 𝓞 E, Xo.univ.eta (b • a) = Xo.univ.eta a ≫ Xo.univ.t.act.act b) ∧ Xo.univ.eta a ^ l.M = 1 := by
  intro _ E _ _ _ H Dw l Xo a
  have := UnivPol.isReduced Xo
  refine ⟨fun c hc => ?_, fun c => LevelPoints.eta_smul _ c a, LevelPoints.eta_pow _ a⟩
  rw [← LevelPoints.eta_smul]
  exact Xo.univ.eta_ker _ (Submodule.smul_mem_smul hc Submodule.mem_top)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SqDvdSumAlternatingFormsOfKilledLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sq_dvd_sum_EF_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  intro E _ _ _ H Dw n Λ N hU hN hle a a' ha ha'
  obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a).1 ha
  obtain ⟨m', x', v', hv', hav'⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a').1 ha'
  have key : ∑ b, Dw.EF (a b) (a' b)
      = ∑ i, ∑ j, Dw.EF (x i) ((∑ b, H.bar (v i b) * v' j b) • x' j) := by
    simp only [hav, hav', Finset.sum_smul, map_sum, LinearMap.sum_apply, Dw.adj, mul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_comm
  rw [key]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  obtain ⟨w, hw, hvw⟩ := hv i
  obtain ⟨w', hw', hvw'⟩ := hv' j
  obtain ⟨c, hc⟩ := (hU w).1 hw w' hw'
  have hs : (∑ b, H.bar (v i b) * v' j b) = ((N : ℤ) ^ 2) • c := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_sum, map_zsmul, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      hvw, hvw', map_mul, map_natCast, zsmul_eq_mul]
    push_cast
    ring
  rw [hs, smul_assoc, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  first | exact @GlobalTheory.AnVal.rd_fock_of_symLift | exact GlobalTheory.AnVal.rd_fock_of_symLift | (intros; apply GlobalTheory.AnVal.rd_fock_of_symLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  first | exact @GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | exact GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | (intros; apply GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symLift_exists_unique_of_cast (hLaw : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) (K : ℤ) (hK : K = (k : ℤ)) (T : Over S) (x : T ⟶ P.A)
    (hx : x ^ k = 1) :
    (∃ U : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U) ∧
      ∀ U U' : ThetaGrp P.A P.L K T, SymLift P.A P.L K k x U → SymLift P.A P.L K k x U' →
        LB.Gen.Corr P.L _ _ _ _ U.φ U'.φ := by
  subst hK
  refine ⟨exists_symLift_global hLaw S P k hk hu T x hx, ?_⟩
  intro U U' hU hU'
  exact SymLiftOdd.symLift_unique hLaw.globalFns P.isAb P.isLB hk U U' hU hU'

theorem moduli_univ_symLift_global :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  intro hLaw E _ _ _ H Dw l Xo N hN
  obtain ⟨hNoeth, -, hUnit, -, hP⟩ := moduli_univ_polAV E H Dw l Xo
  have := hNoeth
  have hN2 : Odd (N ^ 2) := hN.pow
  have hpos : 0 < N ^ 2 := pow_pos hN.pos 2
  refine hP (fun (A : Over Xo.X) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (_ : ℕ) =>
    ∀ (T : Over Xo.X) (x : T ⟶ A), x ^ (N ^ 2) = 1 →
      (∃ U : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧
        ∀ U U' : ThetaGrp A L ((N : ℤ) ^ 2) T, SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U →
          SymLift A L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr L _ _ _ _ U.φ U'.φ) ?_
  intro P T x hx
  exact symLift_exists_unique_of_cast hLaw Xo.X P (N ^ 2) hN2 (hUnit _ hpos) ((N : ℤ) ^ 2)
    (by push_cast; rfl) T x hx

end GlobalTheory
end
end

