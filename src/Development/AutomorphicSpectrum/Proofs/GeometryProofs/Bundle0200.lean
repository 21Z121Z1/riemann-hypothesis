import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0192
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GramMatrixTwistedLieModels
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0194
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0193
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_gauge_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → ∀ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u → (ax0 t x).appTop.hom u.val = 1 ∧ (ax1 t x).appTop.hom u.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebraStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_model_baseChange_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | exact GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_matrix_gram_normal : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame | exact GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | exact GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CodimOneGramTwistAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem codim_one_gram_twist_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ :=
  PositivityTheory.UnitarySelfGeneration.gram_matrix_twisted_lie_models

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombination
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.VanDescent

theorem exists_closed_mem_notMem : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), LocallyOfFiniteType p → ∀ (U O : Y.Opens), ¬ U ≤ O → ∃ z : Y, IsClosed ({z} : Set Y) ∧ z ∈ U ∧ z ∉ O := by
  intro F _ Y p hp U O hUO
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hzU, hzO⟩ := Set.not_subset.1 hUO
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (O : Set Y)ᶜ)
    ⟨z, hzU, hzO⟩ (U.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
  exact ⟨y, hc, hy, hy'⟩

theorem secVal_eq_zero_of_le {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ}
    {B : LB Y} {O : Y.Opens} (s : B.Sec) (hs : nonzeroLocus s ≤ O) (i : B.ι) (y : CxPts p σ)
    (hy : y ∉ ptsIn p σ O) : secVal p σ s i y = 0 := by
  by_contra h
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · exact hy (ptsIn_mono hs ((secVal_ne_zero_iff s hi).1 h))
  · exact h (by rw [secVal_apply]; exact ev_of_notMem hi _)

theorem vanish_descent : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  intro F _ Y p σ hp B hB O x hx
  let J := {z : Y // IsClosed ({z} : Set Y) ∧ z ∉ O}
  have hpt := fun j : J => GlobalTheory.CompanionTheory.Ar.ClosedPt.exists_residue_eval F Y p σ hp B hB j.1 j.2.1
  choose K instF instA instFD e he_smul he_ne he_pt using hpt
  let G : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    Submodule.span ℂ {f | ∃ s : B.Sec, nonzeroLocus s ≤ O ∧ secVal p σ s = f}
  let Z : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    { carrier := {v | ∀ i y, y ∉ ptsIn p σ O → v i y = 0}
      add_mem' := fun {u v} hu hv i y hy => by simp [hu i y hy, hv i y hy]
      zero_mem' := fun i y _ => rfl
      smul_mem' := fun c v hv i y hy => by simp [hv i y hy] }
  have hGZ : G ≤ Z := Submodule.span_le.2 (by
    rintro _ ⟨s, hs, rfl⟩ i y hy
    exact secVal_eq_zero_of_le s hs i y hy)
  have key : ∀ (n : ℕ) (b : Fin n → B.Sec) (d : Fin n → ℂ) (g : B.ι → CxPts p σ → ℂ), g ∈ G →
      (∑ l, d l • secVal p σ (b l) + g) ∈ Z → (∑ l, d l • secVal p σ (b l) + g) ∈ G := by
    intro n
    induction n with
    | zero => intro b d g hg _; simpa using hg
    | succ m ih =>
      intro b d g hg hv
      by_cases H : ∀ a : Fin (m + 1) → F,
          (∀ j, ∑ l, algebraMap F (K j) (a l) * e j (b l) = 0) → a = 0
      · have hz : ∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ →
            ∑ l, d l * τ (e j (b l)) = 0 := by
          intro j τ hτ
          obtain ⟨y, i, hyz, hy⟩ := he_pt j τ hτ
          have hyO : y ∉ ptsIn p σ O := fun h => j.2.2 (hyz ▸ mem_ptsIn.1 h)
          have h1 := hv i y hyO
          have h2 := hGZ hg i y hyO
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero,
            hy] at h1
          exact h1
        have hd : d = 0 := GlobalTheory.CompanionTheory.Arith.DedekindDescent.linIndep_descent F σ J K (Fin (m + 1)) (fun l j => e j (b l)) H d hz
        subst hd
        simpa using hg
      · push Not at H
        obtain ⟨a, ha0, ha⟩ := H
        have hes : ∀ j, e j (∑ l, algX p ⊤ (a l) • b l) = 0 := fun j => by
          simp only [map_sum, he_smul]
          exact ha0 j
        have hsO : nonzeroLocus (∑ l, algX p ⊤ (a l) • b l) ≤ O := by
          by_contra h
          obtain ⟨z, hzc, hzs, hzO⟩ := exists_closed_mem_notMem F Y p hp _ O h
          exact he_ne ⟨z, hzc, hzO⟩ _ hzs (hes _)
        have hsG : secVal p σ (∑ l, algX p ⊤ (a l) • b l) ∈ G :=
          Submodule.subset_span ⟨_, hsO, rfl⟩
        have hsv : secVal p σ (∑ l, algX p ⊤ (a l) • b l) = ∑ l, σ (a l) • secVal p σ (b l) := by
          simp only [map_sum, secVal_smul]
        rw [hsv] at hsG
        obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 ha
        have hσ : σ (a l₀) ≠ 0 := (map_ne_zero σ).2 hl₀
        obtain ⟨c, hc⟩ : ∃ c, c = d l₀ * (σ (a l₀))⁻¹ := ⟨_, rfl⟩
        have hdc : d l₀ = c * σ (a l₀) := by rw [hc, inv_mul_cancel_right₀ hσ]
        have heq : ∑ l, d l • secVal p σ (b l) + g =
            ∑ i, (d (l₀.succAbove i) - c * σ (a (l₀.succAbove i))) •
              secVal p σ (b (l₀.succAbove i)) + (g + c • ∑ l, σ (a l) • secVal p σ (b l)) := by
          rw [Fin.sum_univ_succAbove _ l₀, Fin.sum_univ_succAbove (fun l => σ (a l) • _) l₀]
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdc]
          module
        rw [heq] at hv ⊢
        exact ih _ _ _ (G.add_mem hg (G.smul_mem c hsG)) hv
  have hxspan : x ∈ Submodule.span ℂ (Set.range (SecC.of p σ : B.Sec → SecC p σ B)) :=
    by rw [SecC.span_range_of (p := p) (σ := σ) (B := B)]; exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hxspan
  choose b hb using fun i => (g i).2
  have hval : SecC.val x = ∑ l, f l • secVal p σ (b l) + 0 := by
    rw [← hfg, add_zero, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l, SecC.val_of]
  have hxZ : SecC.val x ∈ Z := hx
  rw [hval] at hxZ
  have hmem := key n b f 0 G.zero_mem hxZ
  rw [← hval] at hmem
  obtain ⟨m, as, ss, hss⟩ := Submodule.mem_span_set'.1 hmem
  choose t ht1 ht2 using fun j => (ss j).2
  exact ⟨m, as, t, ht1, by rw [← hss]; exact Finset.sum_congr rfl fun j _ => by rw [ht2]⟩

end GlobalTheory.CompanionTheory.VanDescent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt | exact GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecondStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at | exact GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpenStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stable_under_generalization_specialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k)), StableUnderGeneralization U → StableUnderSpecialization U → IsOpen U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | exact GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_degree_bound_char_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F₀ F₁ : Submodule (𝓞 L) B.carrier), IsSubFibre M (flagStep Ω b₀ i) z MB F₀ →
      IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁ → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ φ : F₁ →ₗ[𝓞 L] L, (∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (x : B.carrier) v →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u) →
        ∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * locRatio a w c₀ v) ∧
          ∃ x, v (m : L) * locRatio a w c₀ v ≤ v (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @LevelTowerAlt.nef_fibres_block_embedding | exact LevelTowerAlt.nef_fibres_block_embedding
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem curve0_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 :=
  @PositivityTheory.Xgf.curve_z_ne_zero

end GlobalTheory.CompanionTheory.Ar.Fl
end

