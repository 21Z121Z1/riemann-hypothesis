import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3685
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3591
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDataFrom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatio
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomNonvanishingFromInputsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_nonvanishing_from_inputs : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  first | exact @GlobalTheory.SqTop.BotNeFormula.botNe_of_formula | exact GlobalTheory.SqTop.BotNeFormula.botNe_of_formula | (intros; apply GlobalTheory.SqTop.BotNeFormula.botNe_of_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertibleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
theorem _root_.GlobalTheory.T.exists_finiteEtale_Tj_correspondence_p_invertible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  first | exact @GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | exact GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | (intros; apply GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem exists_tautB_chart_at : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hB, hac, hnt, hC, hV⟩ :=
    GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨k, _, m, e, C₁, ξ, θ, hT, hC₁, hθ, hξ⟩ :=
    GlobalTheory.T.exists_tautological_chart_versality Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS V hB hac C ξV hnt hC
  refine ⟨k, inferInstance, m, e, C₁, ξ, hT, hC₁, ?_⟩
  rw [← hV, ← hξ]
  change _ = ξ.base ((spMap θ).base (closedPoint V))
  have h0 : (spMap θ).base (closedPoint V) = closedPoint (ChartRing k m e) := by
    haveI := hθ
    exact IsLocalRing.comap_closedPoint θ
  rw [h0]

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageConstantTriangleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stage_constant_triangle : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  first | exact @GlobalTheory.SqTower.top_stage | exact GlobalTheory.SqTower.top_stage | (intros; apply GlobalTheory.SqTower.top_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartHit

theorem setup : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (φ : InvFun ℤ) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → S.IsSeparated ∧ LocallyOfFiniteType (π ≫ z) ∧ IsLocallyNoetherian S ∧ Dense (Set.range j) ∧ j ≫ π ≫ z = F.s := by
  intro g n F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨J, -, -, -, -, hproj, hdense, hji, -, -, -⟩ := hBlow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hMin
  have hP := GlobalTheory.ArithCurve.isProper_of_projOver hproj
  have hlft : LocallyOfFiniteType (π ≫ z) := GlobalTheory.isProjOver_locallyOfFiniteType _ _ _ hproj
  haveI : IsNoetherianRing (cycAway n) := is_noetherian_subring_closure _ (Set.toFinite _)
  refine ⟨⟨by rw [← terminal.comp_from (π ≫ z)]; infer_instance⟩, hlft, LocallyOfFiniteType.isLocallyNoetherian (π ≫ z), hdense, ?_⟩
  rw [← Category.assoc, hji, hiz]

theorem away_hom_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (t : R), t ≠ 0 → ∀ (l : Localization.Away t →+* FractionRing R), l.comp (algebraMap R (Localization.Away t)) = algebraMap R (FractionRing R) → ∀ (S : Scheme.{0}) [S.IsSeparated] (a b : Sp (Localization.Away t) ⟶ S), spMap l ≫ a = spMap l ≫ b → a = b := by
  intro R _ _ t ht l hl S _ a b h
  haveI : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hinj : Function.Injective l := by
    refine (injective_iff_map_eq_zero l).2 fun x hx => ?_
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) x
    have h1 : IsLocalization.mk' (Localization.Away t) r s * algebraMap R _ (s : R) = algebraMap R _ r :=
      IsLocalization.mk'_spec _ r s
    have h2 : algebraMap R (FractionRing R) r = 0 := by
      rw [← hl, RingHom.comp_apply, ← h1, map_mul, hx, zero_mul]
    have h3 : r = 0 := IsFractionRing.injective R (FractionRing R) (by rw [h2, map_zero])
    show IsLocalization.mk' (Localization.Away t) r s = 0
    rw [h3, IsLocalization.mk'_zero]
  have : IsDominant (spMap l) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap l) h

end GlobalTheory.ChartHit

namespace GlobalTheory.ChartHit

theorem lowBase_regular {n : ℕ} (L : LowBase (zetaAway n) n) : IsRegularLocalRing L.W := by
  haveI : IsNoetherianRing L.W := L.noeth
  let y := L.u (closedPoint L.W)
  let φ₀ := (Scheme.stalkClosedPointTo L.u).hom
  haveI : IsRegularLocalRing ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk L.F y
  have het := L.u_et
  letI : Algebra ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := φ₀.toAlgebra
  haveI : Module.Flat ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := het.1
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm

theorem chart : ∀ {g n : ℕ} (φ : InvFun ℤ), 3 ≤ n → ∀ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)), L.h + L.T.r = g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) → (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) → IsCN V' → IsLocalHom κ → (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) → DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e → ∃ (C : Taut (zetaAway n) g n φ) (θ : C.R →+* V') (e' : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), IsLocalHom θ ∧ (∀ k, θ (C.s k) ≠ 0) ∧ θ.comp C.b = κ.comp L.T.b ∧ DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e' := by
  intro g n φ hn L m N ε V' _ _ _ κ sv D' e hgen hcone hdef hV hκ hs1 hs2 hD
  haveI : IsRegularLocalRing L.W := lowBase_regular L
  have hψV : IsLocalHom ((MvPolynomial.eval₂Hom κ sv).comp MvPolynomial.C) := by
    rw [MvPolynomial.eval₂Hom_comp_C]; exact hκ
  obtain ⟨R, _, _, _, ψ, θ, hcompl, hθ, hθψ, hψl⟩ :=
    GlobalTheory.TChart.exists_complAt_factor_of_isAdicComplete L.W (Fin m ⊕ Fin N) V' hV.2.2.1 (MvPolynomial.eval₂Hom κ sv) hψV
  have hθX : ∀ k, θ (ψ (MvPolynomial.X k)) = sv k := fun k => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = κ := by
    rw [← RingHom.comp_assoc, hθψ, MvPolynomial.eval₂Hom_comp_C]
  have hne : ∀ k, ψ (MvPolynomial.X k) ≠ 0 := fun k h => by
    have h' := hθX k
    rw [h, map_zero] at h'
    rcases k with k | k
    · exact (hs1 k).2 h'.symm
    · exact (hs2 k).ne_zero h'.symm
  obtain ⟨Q, eQ, hQ⟩ := GlobalTheory.TChart.FromEx.exists_dataFrom L.T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n hne (fun k a b => (ε k).2.1 a b)
  have hbd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R := fun k =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 (hs1 k).1 (hθX (.inl k) ▸ hu.map θ)
  have htor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k))) := fun k =>
    isUnit_of_map_unit θ _ (by rw [hθX]; exact hs2 k)
  let C : Taut (zetaAway n) g n φ :=
    { toLowBase := L
      genus := hgen
      m := m
      N := N
      ε := ε
      cone := hcone
      defin := hdef
      R := R
      ψ := ψ
      compl := hcompl
      ψ_loc := hψl
      bd := hbd
      tor := htor
      Q := Q
      e := eQ
      data := hQ }
  refine ⟨C, θ, e, hθ, fun k => ?_, ?_, ?_⟩
  · show θ (ψ (MvPolynomial.X k)) ≠ 0
    rw [hθX]
    rcases k with k | k
    · exact (hs1 k).2
    · exact (hs2 k).ne_zero
  · show θ.comp ((ψ.comp MvPolynomial.C).comp L.T.b) = κ.comp L.T.b
    rw [← RingHom.comp_assoc, hθC]
  · show DegFrom L.T (θ.comp (ψ.comp MvPolynomial.C)) (fun k => θ (ψ (MvPolynomial.X k)))
      (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e
    rw [hθC, show (fun k => θ (ψ (MvPolynomial.X k))) = sv from funext hθX]
    exact hD

end GlobalTheory.ChartHit

theorem GlobalTheory.TChart.exists_chart_at : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hMin hBlow x
  obtain ⟨hsep, hlft, hln, hdense, hjs⟩ := GlobalTheory.ChartHit.setup F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨T, ξT, b, hx, hTj, hTb⟩ := GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt F S (π ≫ z) j hn hdense hjs x
  have hyb : T.y ≫ F.s = jK T.V ≫ spMap b := by
    rw [← hjs, ← Category.assoc, ← hTj, Category.assoc, hTb]
  obtain ⟨L, m, N, ε, V', _, _, _, f, κ, sv, D', e, G', _, _, πG, A', U', hgen, hcone, hdef, hV', hdvr, hfi, hff, hfl,
    hκl, hκb, hs1, hs2, hU, hD⟩ := GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait g hg φ hφ n hn hodd F T b hyb
  obtain ⟨C, θ, e', hθl, hθs, hθb, hD'⟩ := GlobalTheory.ChartHit.chart φ hn L m N ε V' κ sv D' e hgen hcone hdef hV' hκl hs1 hs2 hD
  obtain ⟨G₁, _, _, P, hMP, hCan, hab, htors⟩ := GlobalTheory.T.exists_mumford_family g n φ hn hodd C
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap f := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') f hle
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq hle a
  have hprod : θ (∏ k, C.t k) ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun k _ => hθs (.inl k)
  have htne : (∏ k, C.t k) ≠ 0 := fun h => hprod (by rw [h, map_zero])
  have hunit : IsUnit ((algebraMap V' (FractionRing V')).comp θ (∏ k, C.t k)) := by
    refine isUnit_iff_ne_zero.2 ?_
    simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hprod) :
      algebraMap V' (FractionRing V') (θ (∏ k, C.t k)) ≠ 0)
  let κ' : Localization.Away (∏ k, C.t k) →+* FractionRing V' := IsLocalization.Away.lift (∏ k, C.t k) hunit
  have hκ' : κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = (algebraMap V' (FractionRing V')).comp θ :=
    IsLocalization.Away.lift_comp (∏ k, C.t k) hunit
  have hSF := GlobalTheory.T.trait_chart_generic_fibres_same F C G₁ P hMP hCan T V' θ f fK hV' hθl hθs hfK D' e' hD' G' πG A' U' hU
  have hx₀ : (spMap fK ≫ T.y) ≫ F.s = spMap ((κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) := by
    rw [Category.assoc, hyb, hκ', RingHom.comp_assoc, hθb, hκb]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [hfK]
  rw [← hκ'] at hSF
  obtain ⟨c, hc, hiso, hpt⟩ := GlobalTheory.T.exists_level_abelianLocus_toroidalChart hn hodd F C G₁ P hMP hab htors (FractionRing V') κ' (spMap fK ≫ T.y) hx₀ hSF
  obtain ⟨y, α₁, yU, l, hFam, hSPB, hl, hyl⟩ := GlobalTheory.T.exists_siegelLevelStructure_mumfordFamily_tautological g n φ hn hodd F C G₁ P hMP hab c hc hiso
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.exists_ext_normalised_blowup g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hMin hBlow C G₁ y α₁ hFam
  have hsA : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl]
  have hyUs : yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl (Sp (cycAway n)) _ _ ?_
    have h := hFam.2.2.2.2
    rw [hyl, Category.assoc] at h
    rw [h, ← hsA]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc]
  have hκy := hpt yU hSPB hyUs
  have hξU : spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) ≫ ξ = yU ≫ j := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl S _ _ ?_
    rw [← Category.assoc, hsA, ← hξ, hyl, Category.assoc]
  have hgen' : jK V' ≫ (spMap θ ≫ ξ) = jK V' ≫ (spMap f ≫ ξT) := by
    have e1 : jK V' ≫ spMap θ = spMap κ' ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ']
    have e2 : jK V' ≫ spMap f = spMap fK ≫ jK T.V := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; ext a; simp [hfK]
    rw [← Category.assoc, e1, Category.assoc, hξU, ← Category.assoc, hκy, ← Category.assoc, e2, Category.assoc,
      Category.assoc, hTj]
  have hdom : IsDominant (jK V') := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).le.trans bot_le)⟩
  have hext : spMap θ ≫ ξ = spMap f ≫ ξT :=
    ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (jK V') hgen'
  refine ⟨C, G₁, inferInstance, y, α₁, ξ, hFam, hξ, ?_⟩
  have h1 : (spMap θ).base (closedPoint V') = closedPoint C.R := IsLocalRing.comap_closedPoint θ
  have h2 : (spMap f).base (closedPoint V') = closedPoint T.V := IsLocalRing.comap_closedPoint f
  rw [← hx, ← h1, ← h2]
  show (spMap θ ≫ ξ).base (closedPoint V') = (spMap f ≫ ξT).base (closedPoint V')
  rw [hext]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  first | (exact @GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (exact GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (intros; apply GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdealStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.logKS_inj_mod_maximal | exact GlobalTheory.logKS_inj_mod_maximal | (intros; apply GlobalTheory.logKS_inj_mod_maximal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d → (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)) (j : Xo.XF c ⟶ S), GlobalTheory.Poinc.IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → IsProper π → j ≫ π = C.iF → IsOpenImmersion j → π ⁻¹' Set.range C.iF = Set.range j → GlobalTheory.UChart.SepB Xo c φ j) := by
  first | exact @GlobalTheory.USep.sepB_of_normBl | exact GlobalTheory.USep.sepB_of_normBl | (intros; apply GlobalTheory.USep.sepB_of_normBl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
end
end

