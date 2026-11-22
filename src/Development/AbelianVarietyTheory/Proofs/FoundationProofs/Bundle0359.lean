import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasVal_of_irreducible {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ ϖ' : V}
    (h : Irreducible ϖ) (h' : Irreducible ϖ') {x : FractionRing V} {n : ℤ} (hx : HasVal ϖ' x n) : HasVal ϖ x n := by
  obtain ⟨v, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible V h h'
  obtain ⟨u, rfl⟩ := hx
  refine ⟨v ^ n * u, ?_⟩
  have e : algebraMap V (FractionRing V) ((v ^ n : Vˣ) : V) = algebraMap V (FractionRing V) v ^ n := by
    have := congrArg Units.val (map_zpow (Units.map (algebraMap V (FractionRing V)).toMonoidHom) v n)
    rwa [Units.val_zpow_eq_zpow_val] at this
  rw [Units.val_mul, map_mul, map_mul, mul_zpow, e, _root_.mul_assoc]

theorem nonempty_sabMap_of_models {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (m1' : SABMap t' Xo.univ.t x) (m2' : SABMap t' G' (spMap (algebraMap T.V T.Fr))) :
    Nonempty (SABMap G' G (𝟙 _)) := by
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ (𝟙 _) m1 ((Category.id_comp x).symm ▸ m1')
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 k
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1'.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G' G t' hp m2'
    (Category.id_comp (spMap (algebraMap T.V T.Fr)) ▸ n)
  exact ⟨ψ⟩

theorem HasPhi.unique {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {φ φ' : ℝ} (h : HasPhi y φ)
    (h' : HasPhi y φ') : φ = φ' := by
  obtain ⟨G, t, m1, m2, P, ϖ, Q, β, hϖ, hQ, -, hβ, rfl⟩ := h
  obtain ⟨G', t', m1', m2', P', ϖ', Q', β', hϖ', hQ', -, hβ', rfl⟩ := h'
  obtain ⟨ψ⟩ := nonempty_sabMap_of_models m1 m2 m1' m2'
  obtain ⟨d, hd⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H T.V G G' ψ P P' inferInstance inferInstance inferInstance
  have hQQ : ∀ χ, Q' (d χ) = Q χ := fun χ => by
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main T.V P.D inferInstance χ).1
    obtain ⟨u, hu⟩ := hd χ r hr
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_coord (hQ χ) hr) u
    have h2 := hasVal_of_irreducible hϖ hϖ' (GlobalTheory.ValForm.hasVal_coord (hQ' (d χ)) hu)
    rw [← map_mul, _root_.mul_comm] at h1
    exact hasVal_unique hϖ h2 h1
  obtain ⟨β₁, hβ₁, hφ⟩ := GlobalTheory.EtaVal.phiC_smul_pull E _ _ _ d β' 1 zero_le_one
  have hdiag : ∀ a, β₁.1 a a = β.1 a a := fun a => by
    rw [hβ₁, hβ', hβ, hQQ, _root_.one_mul]
  have e : β₁ = β := by
    refine Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun b => ?_)
    have h1 := hdiag (a + b)
    have s1 := β₁.2.1 a b
    have s2 := β.2.1 a b
    simp only [map_add, LinearMap.add_apply] at h1
    linarith [hdiag a, hdiag b]
  rw [← e, hφ, _root_.one_mul]

theorem exists_ext_hasPhi {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
      i.Finite ∧ OverLa la T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
      (letI := io.toAlgebra; letI := (i.comp io).toAlgebra;
        FrMap ({ i with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 y'.1) ∧
      ∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f →
        evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f) := by
  let _ := H.starRing
  obtain ⟨T', i, y', e', hi, ho', hy', -, hm, hv, C, -, P, -⟩ :=
    GlobalTheory.IntegralExt.exists_ext_chart_unif E H Dw l Xo c T io y la e ho hy
  obtain ⟨φ, hφ⟩ := exists_hasPhi y' C.I.G C.I.t' C.I.m1 C.I.m2 P
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, hm, hv⟩

theorem hasPhi_exists_ext_and_unique :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      (∀ (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∀ y : IntFr Xo c T io, y.IsAlg →
          ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
            i.Finite ∧ OverLa la.1 T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
            ∀ (w : Ix Dw → ℤ) (f : Rul Xo c), f ∈ secZ Xo c w →
              evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f)) ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ φ' : ℝ), HasPhi y φ → HasPhi y φ' → φ = φ' := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun p la T io e ho y hy => ?_, fun _ _ _ _ _ => HasPhi.unique⟩
  obtain ⟨T', i, e', y', φ, hi, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, fun w f hf => hv f hf.1⟩

end GlobalTheory.SlopeRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBoundStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicValuation_thetaKernelJet_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  first | exact @GlobalTheory.NormSum.Term.term_bound | exact GlobalTheory.NormSum.Term.term_bound | (intros; apply GlobalTheory.NormSum.Term.term_bound <;> assumption)
end

