import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

theorem ann_depLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
    ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi e he y hy h u hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have h1 := h (e • u) (hu.2 e he)
  rw [smul_smul, hee, symplO_smul_half _ _ e u y hy] at h1
  exact h1

set_option maxHeartbeats 1000000 in

theorem cosDual : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hyp x hx
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨X, hXdef⟩ : ∃ X : WO (G.pS (.core i)) (G.pT (.core i)), X = e • x₀.map (incA D) := ⟨_, rfl⟩
  have hXh : IsHalf e X := fun a b => by
    simp only [hXdef, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨Z, hZdef⟩ : ∃ Z : WO (G.pS (.core i)) (G.pT (.core i)), Z = X - actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := ⟨_, rfl⟩
  have hZ : IsHalf e Z := fun a b => by
    simp only [hZdef, Matrix.sub_apply, mul_sub, hXh a b, half_actO _ _ e g X hXh a b]
  have key : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1 := by
    intro y hy h1 h2
    have hy' : IsHalf (cA D e) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g⁻¹ y) := half_actO _ _ _ _ _ hy
    have hA := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he y hy h1
    have hB := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he _ hy' (fun v hv => by
      have h3 := h2 v hv
      rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g (e • v) (actO _ _ 1 g⁻¹ y), actO_inv]
      exact h3)
    have H := hyp y hy hA hB
    rw [← hXdef] at H
    rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g X (actO _ _ 1 g⁻¹ y), actO_inv] at H
    have hsum : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by
      rw [hZdef]; abel
    have hs : symplO (G.pS (.core i)) (G.pT (.core i)) X y =
        symplO (G.pS (.core i)) (G.pT (.core i)) Z y +
          symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y := by
      conv_lhs => rw [hsum]
      exact GlobalTheory.LatVac.symplO_add_left _ _ _ _ _
    rw [hs, AddChar.map_add_eq_mul] at H
    generalize hcdef : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c at H
    have hc : c ≠ 0 := by
      intro h0
      have h5 : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) *
          W.ψ (-(symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y)) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      rw [show W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c from hcdef,
        h0, zero_mul] at h5
      exact zero_ne_one h5
    have H' : (W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) - 1) * c = 0 := by
      rw [sub_mul, H, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 H').resolve_right hc)
  obtain ⟨a, ha, b, hb, hZeq⟩ := GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator D hq T L μ0 hL sc G W M hM i hi e he g Z hZ key
  have heq : e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - a) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - -b)) := by
    rw [smul_sub, sub_neg_eq_add, smul_add, actO_add, ← hXdef]
    have h6 : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by rw [hZdef]; abel
    rw [hZeq] at h6
    conv_lhs => rw [h6]
    abel
  obtain ⟨a₁, h1, a₂, h2, heq2⟩ := GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g a ha (-b) (neg_mem hb) heq
  exact GlobalTheory.T.gridCoreNode_unitReading_integral_congruent D hq T L μ0 hL sc G W M hM i hi e he g a₁ h1 a₂ h2 heq2 x hx

end GlobalTheory.CosDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoversAtOverField
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverOverField

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover GlobalTheory.TwistField

section Roots

theorem prim_mul {L : Type} [Field L] {a b : ℕ} (hab : Nat.Coprime a b) (ha : ∃ z : L, IsPrimitiveRoot z a)
    (hb : ∃ z : L, IsPrimitiveRoot z b) : ∃ z : L, IsPrimitiveRoot z (a * b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  have h := (Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [← hx.eq_orderOf, ← hy.eq_orderOf]; exact hab)
  rw [← hx.eq_orderOf, ← hy.eq_orderOf] at h
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem prim_prod {L : Type} [Field L] (s : Finset ℕ) (hp : ∀ q ∈ s, q.Prime) (hz : ∀ q ∈ s, ∃ z : L, IsPrimitiveRoot z q) :
    ∃ z : L, IsPrimitiveRoot z (∏ q ∈ s, q) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine prim_mul ?_ (hz a (Finset.mem_insert_self _ _))
      (ih (fun q hq => hp q (Finset.mem_insert_of_mem hq)) (fun q hq => hz q (Finset.mem_insert_of_mem hq)))
    refine Nat.Coprime.prod_right fun q hq => ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self _ _)) (hp q (Finset.mem_insert_of_mem hq))).2
      (fun h => ha (h ▸ hq))

theorem mem_range_of_pow {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ} (hn : 0 < n) (hz : ∃ z : L, IsPrimitiveRoot z n)
    {w : ℂ} (hw : w ^ n = 1) : w ∈ σ.fieldRange := by
  obtain ⟨z, hz⟩ := hz
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective σ.injective).eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow]; exact hi⟩

end Roots

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_fun_of_val {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hlev : d.IsLev) (hA : d.l₂.A = 1) (hcl : FnAlgClosed d.Xo₂ d.c₂)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
      xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (m : ℕ) (hm : 0 < m) (h3 : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
    (hz : ∀ g : GA D V, ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) ∈ c.F) :
    ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
      ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
        IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
        ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
          (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
              (IntermediateField.inclusion d.c₂.le).toRingHom)
            (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
          (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
          (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
          (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
          ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
            rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
              1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ hz h⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', C.unf un, dict, hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [← hCι, ← hCx]
    exact hdl
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem prim_tupPrime (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) :
    ∃ z : D.what₂.LL, IsPrimitiveRoot z (tupPrime R t) := by
  refine prim_prod _ (fun q hq => ?_) fun q hq => ?_
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨⟨q, hq, he, -⟩, -⟩ := h PP hPP
    exact he ▸ hq
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    exact hr t PP (Or.inr hPP)

end Real

section Cover

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem exists_coeff_cover (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) (c' : Coeff T.Q.l)
    (hc : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (l₂ : Level T.Q.H) (hM : l₂.M = T.Q.l.M * tupPrime R t) (hA : l₂.A = 1)
    (hcop : Nat.Coprime T.Q.l.M (tupPrime R t)) :
    ∃ c₂ : Coeff l₂, c₂.F = D.what₂.embLL.toRatAlgHom.fieldRange := by
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  have hM' : T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero hM0.ne' T.Q.l.A_pos.ne'
  have h1 : ∃ z : D.what₂.LL, IsPrimitiveRoot z T.Q.l.M := by
    have hz := c'.zeta_mem
    rw [hc] at hz
    obtain ⟨y, hy⟩ := hz
    have hp : IsPrimitiveRoot y T.Q.l.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := D.what₂.embLL) (by
        have : D.what₂.embLL y = zeta T.Q.l.M' := hy
        rw [this]; exact Complex.isPrimitiveRoot_exp _ hM') D.what₂.embLL.injective
    obtain ⟨k, hk⟩ : T.Q.l.M ∣ T.Q.l.M' := Nat.dvd_lcm_left _ _
    exact ⟨y ^ k, hp.pow (Nat.pos_of_ne_zero hM') (by rw [hk, mul_comm])⟩
  have h2 := prim_mul hcop h1 (prim_tupPrime R t h hr)
  have hM2 : l₂.M' = T.Q.l.M * tupPrime R t := by simp [Level.M', hA, hM]
  have hpos : 0 < T.Q.l.M * tupPrime R t := hM ▸ lt_of_lt_of_le (by norm_num) l₂.three_le
  refine ⟨⟨c'.F, c'.fin, c'.conj, ?_, ?_⟩, hc⟩
  · rw [hc, hM2]
    exact mem_range_of_pow D.what₂.embLL hpos h2 (Complex.isPrimitiveRoot_exp _ hpos.ne').pow_eq_one
  · refine IntermediateField.adjoin_le_iff.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact c'.le (IntermediateField.subset_adjoin _ _ (by simp))
    · rw [hA]
      have : zeta 1 = 1 := (pow_one _).symm.trans (Complex.isPrimitiveRoot_exp 1 one_ne_zero).pow_eq_one
      rw [this]; exact c'.F.one_mem

end Cover

set_option maxHeartbeats 1000000 in

theorem coversAt_over_field (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hr : R.fam_roots) (hV : XiVal R) (hC : CoverField T R) (i : Fin D.R.m) (n : ℕ)
    (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (tupPrime R t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hc' : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) :
    CoversAt T R i n (tupPrime R) I l₂ c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key : ∀ t, ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = tupPrime R t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧
      d.l₂.A = 1 ∧ FnAlgClosed d.Xo₂ d.c₂ ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₂, hc₂⟩ := exists_coeff_cover T R t (hL.Q_pl t) hr c' hc' (l₂ t) l2 l6 l3.symm
    obtain ⟨d, a1, a2, a3, -, -, -, a4, a5⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n
      (tupPrime R t) (I t) (l₂ t) Xo₂ c₂ (hc₂.trans hc'.symm) l1 l2 l3 l4 l5
    exact ⟨d, a1, a2, a3, a4, a3 ▸ l6, hC i t d.l₂ (a3 ▸ l1) (a3 ▸ l2) (a3 ▸ l6) _ _ (d.hF.trans hc'), a5⟩
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH t).2.1 PP hPP ?_
    have h1 : (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d t).l₂.Mb :=
      Ideal.mul_le_left ((d t).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 t).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  have hval : ∀ t (g : GA D (Wc D i)),
      ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) ∈ c'.F := fun t g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    rw [hx1 t g x hx, hc']
    exact hV t x
  choose f b1 b2 U₂ dict₂ b3 using fun t =>
    exists_fun_of_val (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a4 t) (a5 t) (a6 t) (xi t)
      (hx2 t _ (d t).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t) (hval t)
  refine ⟨fun t => { d t with cδ := f t }, U₂, dict₂, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 t, a7 t⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b3⟩, fun t => (b3 t).2.1, fun t => ⟨m t, hm t, b2 t⟩⟩
  change HalfIs R t T.Q.l.Mb (d t).I
  rw [a2]
  exact hH t

end GlobalTheory.CoverOverField

section Target
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CoverOverField.coversAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → R.fam_roots → GlobalTheory.TwistField.XiVal R → GlobalTheory.TwistField.CoverField T R → ∀ (i : Fin D.R.m) (n : ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H), (∀ t, GlobalTheory.CoverHalf.IsCoverLevel T.Q.l (GlobalTheory.TwistField.tupPrime R t) (I t) (l₂ t)) → (∀ t, HalfIs R t T.Q.l.Mb (I t)) → ∀ (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c'.F = D.what₂.embLL.toRatAlgHom.fieldRange → GlobalTheory.TupleCover.CoversAt T R i n (GlobalTheory.TwistField.tupPrime R) I l₂ c' hle :=
  fun _ _ _ _ _ _ _ T _ R hT hL hr hV hC i n I l₂ hl hH c' hle hc' =>
    GlobalTheory.CoverOverField.coversAt_over_field T R hT hL hr hV hC i n I l₂ hl hH c' hle hc'

end Target
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_K_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.cuspKFin_decomp | exact GlobalTheory.KFinDecomp.cuspKFin_decomp | (intros; apply GlobalTheory.KFinDecomp.cuspKFin_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DblHandOfChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem dbl_hand_of_chars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (σ j : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (χz : (AE D)ˣ →* Circle)
    (hz : IsHeckeChar D χz) (hzr : ResEta D χz 1)
    (e1 : G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz) (e2 : G.chrT (.mu t D.R.m j) = G.chrT (.top t j))
    (e3 : G.chrS (.mu t D.R.m (j + 1)) = G.chrS (.top t (j + 1)))
    (e4 : G.chrT (.mu t D.R.m (j + 1)) = G.chrT (.top t (j + 1)) * χz) : ∀ (vN : VolN (besDecAt G j (σ + 1) hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ) (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.top j)) φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))),
      Chain.hand (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
        (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
        (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        Φ₁ Φ₂ φ g h₁ h₂ =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h₁) Φ₁))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
            (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h₁, h₂) Φ₂))) := by
  intro vN Φ₁ Φ₂ φ hΦ₁ hΦ₂ hφ g h₁ h₂
  have rA : Pair.InRange D.R.m (.top t j) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have rB : Pair.InRange D.R.m (.top t (j + 1)) := by
    simp [Pair.InRange, Pair.big, Node.InRange]; omega
  have hA := Wl.om_is (.top t j) rA
  have hB := Wl.om_is (.top t (j + 1)) rB
  have hoa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.mu t D.R.m j))
      (Wl.om (.top t j)) := e2 ▸ hA
  have hob : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.mu t D.R.m (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := e3 ▸ hB
  obtain ⟨omz, hoz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.mu t D.R.m j)) Wl.ψ_std hz hoa.hecT hzr hoa.resT
  obtain ⟨omz', hoz'⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (GlobalTheory.SeeSaw.Model.nLine D) Wl.ψ
    (G.chrS (.mu t D.R.m (j + 1))) χz Wl.ψ_std hob.hecS hz hob.resS hzr
  have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) Wl.ψ
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
  let s₁ : StepBF Wl.ψ B J :=
    stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : StepFB Wl.ψ J B' :=
    stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have hΞ₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) :=
    hth.1 (σ + 1) B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  have hΞ₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) :=
    hth.2 σ J B' s₂ _ (s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂)
  funext h₂'
  exact (GlobalTheory.Unf.Contr.contrLaw D Wl.ψ σ B J B' s₁ s₂ (linkAt hM j σ hj vN (by omega) _)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) (G.chrS (.top t j)) (G.chrT (.top t (j + 1))) χz
    (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omz' e1 e4 hoa hoz hob hoz' φ _ _ hφ hΞ₁ hΞ₂).2.2 h₂'

end GlobalTheory.RowChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferredStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  first | exact @GlobalTheory.EvenOnto.upPar_of_transfer | exact GlobalTheory.EvenOnto.upPar_of_transfer | (intros; apply GlobalTheory.EvenOnto.upPar_of_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanMatricesTripleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_matrices_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : NumberField.InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : NumberField.InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c := by
  first | exact @GlobalTheory.RealLift.FockFirst.exists_fockMap_first | exact GlobalTheory.RealLift.FockFirst.exists_fockMap_first | (intros; apply GlobalTheory.RealLift.FockFirst.exists_fockMap_first <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  first | exact @GlobalTheory.SeeConj.exists_frame_symLevel | exact GlobalTheory.SeeConj.exists_frame_symLevel | (intros; apply GlobalTheory.SeeConj.exists_frame_symLevel <;> assumption)
end

