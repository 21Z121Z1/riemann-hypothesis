import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionLemmaOfWittCoreDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem transvTrivial_of_descent (D : D7) (hD : Descent D) : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvTrivial D := by
  intro S S₀ T ρ d ψ χS χT om hom μ 𝓕 hμ a v hv u hu x hx f hf
  obtain ⟨om₀, hom₀⟩ := (hD ψ S T χS χT om hom).1 S₀ ρ d
  obtain ⟨m, b, c, rfl, hdet, hk⟩ := GlobalTheory.T.unitaryTransvection_eq_leviUnipotentProduct D S S₀ ρ d _ v hv u hu
  obtain ⟨h1, h2, h3⟩ := hk T x hx
  have F := fun g hg => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ g hg
  have hc := hom.om_pres (d.nC c, 1) f hf
  have hb := hom.om_pres (d.nB b, 1) _ hc
  have e : om (d.levi m * d.nB b * d.nC c, 1) f = om (d.levi m, 1) (om (d.nB b, 1) (om (d.nC c, 1) f)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one, mul_one]
  have hq : symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) = 0 := h3
  rw [e, (F _ hb).levi, h1, (F _ hc).unip, h2, GlobalTheory.MixPer.heisO_zero, (F _ hf).centre, hq, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet]
  simp

theorem transvLemma_of_descent : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvLemma D := fun D hD =>
  ⟨(GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).1, (GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).2, transvTrivial_of_descent D hD⟩

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_family_vacuum_data : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : AllTrue W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (pk W).ΛX) (pk W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  first | exact @GlobalTheory.XGeoStd.Frames.exists_locX_std | exact GlobalTheory.XGeoStd.Frames.exists_locX_std | (intros; apply GlobalTheory.XGeoStd.Frames.exists_locX_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_chain_descent : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (pk W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (pk W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (pk W).ψ _ _ (comb (pk W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @GlobalTheory.Fam.VacTheta.main | exact GlobalTheory.Fam.VacTheta.main | (intros; apply GlobalTheory.Fam.VacTheta.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryClassRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiCol

theorem colLam_ne_zero {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : colLam T v g ≠ 0 := by
  unfold colLam
  split_ifs with h
  · simp only [Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    intro h0
    have e := (T.gl.psi0 h.choose v h.choose_spec).map_add_eq_mul
      (∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0)
      (-(∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at e
    exact one_ne_zero e
  · exact one_ne_zero

theorem mem_type_prod_iff {D : D7} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ↔ ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, Fin.exists_fin_two]

theorem trace_chi_col_factor : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u) (y : (F0 W u).cls0.lev.U), (((F0 W u).cls0.lev.chi y : ℂˣ) : ℂ) * ∏ i : Fin a.n, GlobalTheory.FamTraceChiCol.colLam (F0 W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) y.1 = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a y
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg := hA.lev.1
  set w : Fin a.n → IsDedekindDomain.HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) := fun i => (a.pl i).1.under (𝓞 (I.rec7 l Z).host.F) with hw
  have hw_mem : ∀ i, (((I.rec7 l Z).host.g 0 * (I.rec7 l Z).host.g 1 : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (w i).asIdeal := by
    intro i
    have h1 := hTP.1 (a.pl i).1 (a.pl i).2
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact h1
  have hw_inj : Function.Injective w := by
    intro i i' hii
    obtain ⟨PP, _, hu⟩ := hTP.2 (w i) (hw_mem i)
    have e1 := hu (a.pl i).1 ⟨(a.pl i).2, rfl⟩
    have e2 := hu (a.pl i').1 ⟨(a.pl i').2, hii.symm⟩
    exact a.pl.injective (Subtype.ext (e1.trans e2.symm))
  set S : Fin 2 → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) :=
    fun j => {v | ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal} with hS
  have hrange : S 0 ∪ S 1 = Set.range w := by
    ext v
    simp only [Set.mem_union, hS, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hv
      have hv' : (((I.rec7 l Z).host.g 0 * (I.rec7 l Z).host.g 1 : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := (mem_type_prod_iff v).2 (Fin.exists_fin_two.2 hv)
      obtain ⟨PP, ⟨hPP, hPv⟩, _⟩ := hTP.2 v hv'
      exact ⟨a.pl.symm ⟨PP, hPP⟩, by simp [hw, hPv]⟩
    · rintro ⟨i, rfl⟩
      exact Fin.exists_fin_two.1 ((mem_type_prod_iff (w i)).1 (hw_mem i))
  have hfin : ∀ j, (S j).Finite := fun j =>
    (Set.finite_range w).subset (hrange ▸ (by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> subst hj
      · exact Set.subset_union_left
      · exact Set.subset_union_right))
  have hdisj : Disjoint (S 0) (S 1) := by
    rw [Set.disjoint_left]
    intro v h0 h1
    exact absurd (type_idx_unique (D := I.rec7 l Z) h0 h1) (by decide)
  have hinner : ∀ j : Fin 2,
      (∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
        (Formalism.L2.Forms.lamJ ((F0 W u).gl.psi0 j v h) ((F0 W u).gl.chiB j v h) (I.rec7 l Z).R.k (I.rec7 l Z).R.t 0 (I.rec7 l Z).R.k
          (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat j v h ((F0 W u).glev0.fr j v h)
            (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))))⁻¹) =
      ∏ᶠ v ∈ S j, (colLam (F0 W u) v y.1)⁻¹ := by
    intro j
    refine finprod_congr fun v => finprod_congr fun h => ?_
    rw [colLam_eq (F0 W u) j h y.1]
  have hchi := (F0 W u).glev0.chi_eq y
  rw [Fin.prod_univ_two, hinner 0, hinner 1, ← finprod_mem_union hdisj (hfin 0) (hfin 1), hrange,
    finprod_mem_range hw_inj, finprod_eq_prod_of_fintype] at hchi
  rw [hchi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (colLam_ne_zero (F0 W u) _ _)

end GlobalTheory.FamTraceChiCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.KomExist

theorem even_rankX {D : D7} (j : ℕ) (hj : j ≤ D.R.m) : Even (D.sp.X j).rank := by
  rw [Formalism.L2.Forms.rankN D j hj]
  show Even (D.R.k + j * (D.R.t + 1))
  obtain ⟨c, hc⟩ := D.R.t_odd
  exact D.R.k_even.add (Even.mul_left ⟨c + 1, by omega⟩ j)

theorem kom_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (pk W).ψ _ _ (chrK W t j) (chrK W t j) (kom t j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ haT
  have hL := hW.pk.bot.hyp.2.2.2.1.lev
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists (I.rec7 l Z)
  have key : ∀ (t : W.P.T) j, j < B.R.m → ∃ om : Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
      IsWeilDatumO (pk W).ψ _ _ (chrK W t j) (chrK W t j) om := by
    intro t j hj
    have hH := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t ⟨j, hj⟩
    exact hE _ _ (pk W).ψ _ _ haT.pinX.std hH hH
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX j (le_of_lt hj)))
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX (j + 1) hj))
  classical
  refine ⟨fun t j => if h : j < B.R.m then (key t j h).choose else 1, fun t j hj => ?_⟩
  simp only [dif_pos hj]
  exact (key t j hj).choose_spec

end GlobalTheory.Fam.KomExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_index : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((F0 W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  first | exact @GlobalTheory.FamTrace.RedAt.inJ_red | exact GlobalTheory.FamTrace.RedAt.inJ_red | (intros; apply GlobalTheory.FamTrace.RedAt.inJ_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceAtG

theorem mat_embA_besFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) (h : GA D B.A)
    (g₀ : GL n k) (hh : (mt B.A h).map p.π = FA.β * g₀.val * FA.γ) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (GlobalTheory.RootEx.embX c g₀).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  have hint : (mt B.V (B.d.emb0 (B.o.emb (h, 1)))).map p.π * ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) =
      (rat (B.d.i₀ * B.o.iA)).map p.π * FA.β * g₀.val := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, eA, Matrix.map_mul, hh]
    simp only [Matrix.mul_assoc]
    rw [FA.γβ, Matrix.mul_one]
  refine GlobalTheory.LocGrp.eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 hint fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.TraceAtG

end

noncomputable section
open GlobalTheory.FamTrace

theorem GlobalTheory.TraceAtG.levAtG_embA_iff : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FamTrace.LevAtG a (embA a.d.B.d a.d.B.o κ) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∈ a.v.gP) ∧ GlobalTheory.FamTrace.TraceAtG a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  have hmi : ∀ i, 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := fun i => by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega

  have hbes : ∀ i, (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    intro i
    have hm := hmi i
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (pk W) u a.g).B 0 _ hm →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hm _ _
    exact key _ (ha.bot.1 hm) _ _ HEq.rfl HEq.rfl
  have hmat : ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) (embA a.d.B.d a.d.B.o κ)
      (GlobalTheory.RootEx.embX ((a.G i).s + 1) g) := fun i g hg =>
    GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ (hbes i) κ g hg
  have huniq : ∀ i x m m', (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m →
      (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m' → m = m' := by
    intro i x m m' h1 h2
    unfold GLoc.Mat at h1 h2
    rw [h1] at h2
    refine Units.ext ?_
    have := congrArg (fun M => ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ * M *
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β) h2
    simp only [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, Frame.γβ, Matrix.mul_one] using this
  have hex : ∀ i, ∃ g, IsMatrixInFrameOfXZero (a.G i) κ g := fun i =>
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  constructor
  · intro hlev
    have htr : TraceAtG a κ := fun i g hg => hlev i _ (hmat i g hg)
    refine ⟨?_, htr⟩
    have hsd := (ha.x 0 (Nat.zero_le _)).sd
    have hloc : ∀ i, GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.G i).q.v) := by
      intro i
      obtain ⟨g, hg⟩ := hex i
      have hlev0 := htr i g hg
      let β := GlobalTheory.SplitLat.frameOf (a.G i).q ((I.rec7 l Z).sp.X 0) _ ((a.G i).FX 0 (Nat.zero_le _))
      have hIs : β.IsLat (a.g.x 0).L (GlobalTheory.SplitLat.stdLat (a.G i).k _) := fun x => by
        rw [GlobalTheory.SplitLat.mem_std]; exact (a.G i).latX 0 (Nat.zero_le _) x
      have key := GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes _ (a.G i).k (a.G i).q ((I.rec7 l Z).sp.X 0) _ β (a.g.x 0).L _ hsd hIs κ
      refine key.2 ?_
      have hreg := ((Chain.ofType_regular _ _ _ _ _ : ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).Regular).2.2 0
        ((a.G i).s + 1) (Nat.zero_add _)).2.2
      have hst := hreg hlev0
      have hK := GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (a.G i).S.ϖ
        (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (l := (a.G i).s + 1) 0 ((a.G i).s + 1) (Nat.zero_add _)) hst
      have hcoord : coordHom ((I.rec7 l Z).sp.X 0) (a.G i).q.pr β.b β.b' β.bb' β.b'b κ = g :=
        ((eq_coordHom_iff _ _ _ _ _ _ κ g).1 hg).symm
      rw [hcoord]
      exact GlobalTheory.LevX.smul_stdLat_of_mem_KO hK
    intro y hy
    have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua (I.rec7 l Z) (fun p => p ∈ a.v.gP)).2 ((I.rec7 l Z).sp.X 0)).2.2.2 (a.g.x 0).L
    have hy' : ∀ j, (mt ((I.rec7 l Z).sp.X 0) κ *ᵥ y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (fun p => p ∈ a.v.gP) := fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (hy t)
    have hey : ∀ v e, e ∈ GlobalTheory.FinPl.intAt (I.rec7 l Z) (· = v) → ∀ j, (e • y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (· = v) :=
      fun v e he j => by simpa [smul_eq_mul] using Ideal.mul_mem_right (y j) _ he.1
    rw [hlat y hsd.1, hlat _ hsd.1]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      have := h2 _ hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · rintro ⟨-, htr⟩ i m hm'
    obtain ⟨g, hg⟩ := hex i
    rw [huniq i _ _ _ hm' (hmat i g hg)]
    exact htr i g hg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl.PinComb

variable {D : D7} {c : Comm D}

def mxSub (P : GlobalTheory.FinPl.Pl D → Prop) (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | GlobalTheory.FinPl.MxAt P u}
  zero_mem' := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  add_mem' {a b} ha hb := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).add_mem (ha i j) (hb i j)

theorem combAt_aconv {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (l : List (WO S T →₀ ℂ))
    (hl : ∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (aconv l) :=
  GlobalTheory.QPl.ThetaPin.aconv_support (mxSub P S T) l hl

theorem combAt_smul {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (r : ℂ) {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (r • e) :=
  fun u hu => he u (Finsupp.support_smul hu)

theorem combAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} : GlobalTheory.FinPl.CombAt P (0 : WO S T →₀ ℂ) :=
  fun u hu => by simp at hu

theorem combAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P' e :=
  fun u hu => GlobalTheory.DisjComb.mxAt_mono h (he u hu)

theorem combAt_of_isCombAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {q : GlobalTheory.FinPl.SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
    {e : WO S T →₀ ℂ} {Ξ : Matrix Y Y' k → ℂ} (h : (ofSplit q).IsCombAt ψ FS FT e Ξ) : GlobalTheory.FinPl.CombAt (· = q.v) e :=
  fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D k q u (h.1 u hu)

variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

theorem eL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eL j) := by
  obtain ⟨d, hd⟩ : ∃ d, j + d = Q.s := ⟨Q.s - j, by omega⟩
  exact combAt_of_isCombAt (Q.eL_at j d hd)

theorem eT_combAt (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eT j h) := by
  have hj : j = Q.s := by have := Q.hs; omega
  subst hj
  exact combAt_of_isCombAt Q.eLT_at

theorem dL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s + 1) (α : Q.Ch j) (γ : Q.Ch (j + 1)) :
    GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.dL j α γ) := by
  rcases Nat.lt_or_ge j Q.s with h | h
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = Q.s := ⟨Q.s - (j + 1), by omega⟩
    exact combAt_of_isCombAt (Q.dL_mid j d hd α γ)
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      exact combAt_of_isCombAt (Q.dL_pen α γ)
    · have h'' : j = Q.s + 1 := by omega
      subst h''
      exact combAt_of_isCombAt (Q.dL_top α γ)

theorem pinTup_combAt {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ) (j : ℕ) :
    GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQ j) ∧
      (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQT j h)) ∧
      ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).dQ j α γ) := by
  have hQ : ∀ i, (F.Q i).q.v ∈ (F.pinTup sc cT).Q := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hmono : ∀ i {S T : HSp D} {e : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt (· = (F.Q i).q.v) e →
      GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) e :=
    fun i _ _ _ he => combAt_mono (fun p hp => hp ▸ hQ i) he
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨?_, fun h => ?_, fun α γ => ?_⟩
  · show GlobalTheory.FinPl.CombAt _ (if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0)
    split_ifs with hj
    · refine combAt_aconv _ fun e he => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (eL_combAt _ j (by have := hs i; omega))
    · exact combAt_zero
  · show GlobalTheory.FinPl.CombAt _ (aconv (List.ofFn fun i => (F.Q i).eT j h))
    refine combAt_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact hmono i (eT_combAt _ j h)
  · show GlobalTheory.FinPl.CombAt _ (if j < D.R.m then
      (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0)
    split_ifs with hj
    · refine combAt_smul _ (combAt_aconv _ fun e he => ?_)
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (dL_combAt _ j (by have := hs i; omega) _ _)
    · exact combAt_zero

end GlobalTheory.QPl.PinComb

open GlobalTheory.QPl.PinComb in

theorem GlobalTheory.QPl.PinComb.famOf_pinTup_combAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ J _ row col hCh sc cT t j
  exact pinTup_combAt _ sc cT j

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_kernel : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → GlobalTheory.FamTrace.TraceAtG a κ := by
  first | exact @GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem | exact GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem | (intros; apply GlobalTheory.FamTrace.TraceFwd.traceAtG_of_mem <;> assumption)
end

