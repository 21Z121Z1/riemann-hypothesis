import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import GroundTheory.GlobalFields.TateThesis.Bundle0007
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
section
open NumberField Formalism.IndefR.NX

namespace GlobalTheory

theorem isKsForm_of_formsIso {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G') :
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  intro f hA'
  obtain ⟨n, b, hmem, _hKi, hKs, hLi, hLs⟩ := hA'
  have hmem' : ∀ i, f.e.symm (b i) ∈ A.WK := fun i => (f.wk _).2 (by simpa using hmem i)
  have hLi' : LinearIndependent LL (fun i => f.e.symm (b i)) :=
    hLi.map' f.e.symm.toLinearMap (LinearEquiv.ker _)
  refine ⟨n, fun i => f.e.symm (b i), hmem', ?_, ?_, hLi', ?_⟩
  · refine LinearIndependent.restrict_scalars (K := LL) ?_ hLi'
    intro r s h
    have h' : algebraMap Ks LL r = algebraMap Ks LL s := by
      simpa [Algebra.algebraMap_eq_smul_one] using h
    exact (algebraMap Ks LL).injective h'
  · apply le_antisymm
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 hmem')
    · intro y hy
      have hy' : f.e y ∈ Submodule.span Ks' (Set.range b) := by rw [hKs]; exact (f.wk y).1 hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ks').1 hy'
      have hyeq : y = ∑ i, f.eK.symm (c i) • f.e.symm (b i) := by
        have : y = f.e.symm (∑ i, c i • b i) := by rw [hc]; simp
        rw [this, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul LL (c i) (b i), LinearEquiv.map_smul, ← algebraMap_smul LL (f.eK.symm (c i)),
          ← f.eK_LL, RingEquiv.apply_symm_apply]
      rw [hyeq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : Set.range (fun i => f.e.symm (b i)) = f.e.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, show (⇑f.e.symm : WL' → WL) = ⇑(f.e.symm : WL' →ₗ[LL] WL) from rfl, Submodule.span_image, hLs,
      Submodule.map_top, LinearEquiv.range]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def blkIxEquiv (r : ℕ) : UnipotentBlockColumnIndex a r (a - 1) ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2.1⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem blkU_comp_equiv {R : Type} [CommRing R] (r : ℕ) (x : BlockIx a r → R) :
    blkU (fun t => x (blkIxEquiv r t)) = unip x := by
  apply Units.ext
  change 1 + posM Subtype.val (fun t => x (blkIxEquiv r t)) = 1 + nilM x
  congr 1
  have e1 : posM Subtype.val (fun t => x (blkIxEquiv r t)) =
      ∑ s : BlockIx a r, Matrix.single s.1.1 s.1.2 (x s) :=
    Equiv.sum_comp (blkIxEquiv r) (fun s : BlockIx a r => Matrix.single s.1.1 s.1.2 (x s))
  rw [e1]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, nilM, Matrix.of_apply]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro s hs
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hs (Subtype.ext (Prod.ext h1 h2))
  · refine Finset.sum_eq_zero fun s _ => if_neg ?_
    rintro ⟨h1, h2⟩
    apply h
    rw [← h1, ← h2]
    exact s.2

def blkIxHomeo (r : ℕ) : (BlockIx a r → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a r (a - 1) → Ad E) where
  toFun x t := x (blkIxEquiv r t)
  invFun y s := y ((blkIxEquiv r).symm s)
  left_inv x := funext fun s => by simp
  right_inv y := funext fun t => by simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun s => continuous_apply _

theorem blkIxHomeo_mem (r : ℕ) (x : BlockIx a r → Ad E) :
    blkIxHomeo r x ∈ ratV E (UnipotentBlockColumnIndex a r (a - 1)) ↔ x ∈ ratN E a r := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun s => c ((blkIxEquiv r).symm s), funext fun s => ?_⟩
    have := congrFun hc ((blkIxEquiv r).symm s)
    simpa [blkIxHomeo] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkIxEquiv r t), rfl⟩

theorem good_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  intro E _ _ _ a ψ φ h
  have hcont : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN E a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
      (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
    haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTripleForOfOff
section
noncomputable section

namespace GlobalTheory.TripTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms
open Formalism.L2.Host (HChar CharFrame ValLL0 embLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.Triple
open GlobalTheory.EigTie
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW GaloisReps)
open GlobalTheory.LiftLeaf (CommG)
open GlobalTheory.SupLaw (OffRange)
open GlobalTheory.TwistAbove (twGL)

def SigAllAt (D : D7) (i : D.ntw.Tw) : Prop :=
  ∀ j b (x : D.nexp.Fm i j b) (ev : ℕ → PlE D.host → FractionRing (D.ntw.O i)), x ≠ 0 →
    MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b) x = x →
    (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → D.nexp.hkF i j b k P x = ev k P • x) →
    ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P →
      P ∉ D.ntw.S0 i → algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) = ev k P

def MeetsP0 (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  ∀ W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b), W ≠ ⊥ → GStable D.nexp i j b W →
    (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* Gab D.host.E D.nd.Om}

end GlobalTheory.TripTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_frobenius_equation_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  first | exact @GlobalTheory.BSP.Height.bas_frob | exact GlobalTheory.BSP.Height.bas_frob | (intros; apply GlobalTheory.BSP.Height.bas_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
section
noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem theta_unfold_mirabolic (l : Fin a) (_hl : l.val + 1 = a) (P : Subgroup (GL (Fin a) E))
    (hP : ∀ γ : GL (Fin a) E, γ ∈ P ↔ ∀ j, γ.val l j = if j = l then 1 else 0) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)]
    [MeasurableSpace (Fin a → Ad E)] [BorelSpace (Fin a → Ad E)] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ) :
    (∀ F : GA E a × (Fin a → Ad E) → ℝ≥0∞, Measurable F → (∀ γ g y, F (ratGL E a γ * g, y) = F (g, y)) →
      ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
        ∫⁻ g in 𝓕', F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val) ∂μ) ∧
    ∀ F : GA E a × (Fin a → Ad E) → ℂ, Measurable F → (∀ γ g y, F (ratGL E a γ * g, y) = F (g, y)) →
      ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ < ⊤ →
      (∀ᵐ g ∂μ.restrict 𝓕,
        Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
      IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
      IntegrableOn (fun g => F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val)) 𝓕' μ ∧
      ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
        ∫ g in 𝓕', F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val) ∂μ := by
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ P ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [hP, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
  have he : (Pi.single l 1 : Fin a → Ad E) = algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [he]
  have hc : Measurable fun g : GA E a => (g, (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E)) ᵥ* g.val) :=
    measurable_id.prodMk (continuous_vecMul _).measurable
  exact ⟨fun F hm hF => lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕' (fun g y => F (g, y)) hF
      (hm.comp hc).aemeasurable,
    fun F hm hF hfin => integral_tsum_vecMul μ hv hP' h𝓕 h𝓕' (fun g y => F (g, y)) hF
      (hm.comp hc).aestronglyMeasurable hfin.ne⟩

omit [NumberField E] in

theorem exists_mirabolic (l : Fin a) :
    ∃ P : Subgroup (GL (Fin a) E), ∀ γ : GL (Fin a) E, γ ∈ P ↔ ∀ j, γ.val l j = if j = l then 1 else 0 := by
  have h : ∀ γ : GL (Fin a) E, (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 ↔
      ∀ j, γ.val l j = if j = l then 1 else 0 := fun γ => by
    rw [Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
  refine ⟨{ carrier := {γ | (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1}
            mul_mem' := fun {x y} hx hy => ?_, one_mem' := Matrix.vecMul_one _, inv_mem' := fun {x} hx => ?_ }, h⟩
  · simp only [Set.mem_setOf_eq, Units.val_mul, ← Matrix.vecMul_vecMul] at *
    rw [hx, hy]
  · simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

open NumberField Matrix GlobalTheory.MirTower in

theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last

open NumberField Matrix GlobalTheory.MirTower in

theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEulerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.Core := by
  first | exact @GlobalTheory.langRecCore_of_artinReciprocity | exact GlobalTheory.langRecCore_of_artinReciprocity | (intros; apply GlobalTheory.langRecCore_of_artinReciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMtMulLeftAdelicMatrixHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

def matrixColumns (R : Type) [AddCommGroup R] (n m : ℕ) :
    Matrix (Fin n) (Fin m) R ≃+ (Fin m → Fin n → R) where
  toFun x j i := x i j
  invFun y := Matrix.of fun i j => y j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_mul_left_eq_of_mulVec (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    (n m : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ ν : Measure (Fin n → R), ν.IsAddHaarMeasure → ν.map A.mulVecLin = ν)
    (μ : @Measure (Matrix (Fin n) (Fin m) R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Matrix (Fin n) (Fin m) R) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x : Matrix (Fin n) (Fin m) R => A * x) μ = μ := by
  letI mM : MeasurableSpace (Matrix (Fin n) (Fin m) R) := borel _
  haveI bM : BorelSpace (Matrix (Fin n) (Fin m) R) := ⟨rfl⟩
  letI mP : MeasurableSpace (Fin m → Fin n → R) := borel _
  haveI bP : BorelSpace (Fin m → Fin n → R) := ⟨rfl⟩
  let e := matrixColumns R n m
  have he : Continuous e := continuous_pi fun j => continuous_pi fun i =>
    (continuous_apply j).comp (continuous_apply i)
  have hes : Continuous e.symm := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  let φ : (Fin n → R) →+ (Fin n → R) := A.mulVecLin.toAddMonoidHom
  have hφ : Continuous φ := Continuous.matrix_mulVec continuous_const continuous_id
  haveI hν : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have key := map_pi_eq_of_map_addHaar_eq (Fin n → R) φ hφ hA m (μ.map e) hν
  have hΦ : Continuous (fun (x : Fin m → Fin n → R) i => φ (x i)) :=
    continuous_pi fun i => hφ.comp (continuous_apply i)
  have hfac : (fun x : Matrix (Fin n) (Fin m) R => A * x) =
      e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e := by
    funext x
    ext i j
    exact Matrix.mul_apply
  rw [hfac]
  calc μ.map (e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e)
      = ((μ.map e).map (fun (x : Fin m → Fin n → R) i => φ (x i))).map e.symm := by
        rw [Measure.map_map hΦ.measurable he.measurable, Measure.map_map hes.measurable (hΦ.comp he).measurable]
    _ = (μ.map e).map e.symm := by rw [key]
    _ = μ := by
        rw [Measure.map_map hes.measurable he.measurable]
        have : (e.symm ∘ e : Matrix (Fin n) (Fin m) R → _) = id := by
          funext x; simp
        rw [this, Measure.map_id]

theorem map_mt_mul_eq : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D V.rank m)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D V.rank m => (HMul.hMul (mt V g) (x : Matrix (Fin V.rank) (Fin m) (AE D)) : Mx D V.rank m)) = μ := by
  intro D V m g μ hμ
  refine map_mul_left_eq_of_mulVec (AE D) V.rank m (mt V g) ?_ μ hμ
  intro ν hν
  exact PI.VolSemiDirect.W.Cj.unipotent_modulus_holds _ _ D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) g ν hν

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryGramAdelicMatrixHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mul_unitary_map_haar : ∀ (D : D7) (N m : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 → ∀ (g : HA (AF D.host.F) D.sp.cm.sig K) (μ : Measure (Mx D m N)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m N => (HMul.hMul (x : Matrix (Fin m) (Fin N) (AE D)) ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) : Mx D m N)) = μ := by
  intro D N m K hK hdet g μ hμ
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  let A : Matrix (Fin N) (Fin N) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig K g).1
  let φ : (Fin N → AE D) →+ (Fin N → AE D) :=
    { toFun := fun v => Matrix.vecMul v A
      map_zero' := Matrix.zero_vecMul A
      map_add' := fun a b => Matrix.add_vecMul A a b }
  have hφ : Continuous φ := continuous_id.matrix_vecMul continuous_const
  exact GlobalTheory.map_pi_eq_of_map_addHaar_eq (Fin N → AE D) φ hφ
    (fun ν hν => GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm N K ⟨fun i j => hK i j, hdet⟩ g ν hν) m μ hμ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFinite
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RSJ

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem valued_natCast_apply (E : Type) [Field E] [NumberField E] (N : ℕ)
    (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v) = v.valuation E (N : E) := by
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N]
  exact valuedAdicCompletion_eq_valuation' v (N : E)

theorem natLat_iff_mem_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) →
      ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  intro E _ _ N hN J hJ x
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (N : E) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).2 hN0
  have hc : ∀ v : HeightOneSpectrum (𝓞 E),
      exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) = v.valuation E (N : E) := by
    intro v
    rw [hJ, GroundTheory.Global.count_spanSingleton v hN0, neg_neg, exp_log (hc0 v)]
  rw [GroundTheory.Global.mem_idealFiniteAdeles]
  simp only [hc]
  have hunit : (N : FiniteAdeleRing (𝓞 E) E) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N, ← map_mul, mul_inv_cancel₀ hN0,
      map_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ v
    change Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v * z v) ≤ _
    rw [map_mul, valued_natCast_apply]
    have : Valued.v (z v) ≤ 1 := by
      have h := hz v
      rwa [mem_adicCompletionIntegers] at h
    calc v.valuation E (N : E) * Valued.v (z v) ≤ v.valuation E (N : E) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hx
    refine ⟨algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ * x, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers]
      change Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) v * x v) ≤ 1
      rw [map_mul]
      change Valued.v (((N : E)⁻¹ : E) : v.adicCompletion E) * Valued.v (x v) ≤ 1
      rw [valuedAdicCompletion_eq_valuation' v, map_inv₀]
      exact (GroundTheory.Global.inv_mul_le_one_iff_withZero (hc0 v)).2 (hx v)
    · rw [← mul_assoc, hunit, one_mul]

end GlobalTheory.RSJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_image_mem_BdRplus_lattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  first | exact @GlobalTheory.GalStep.main | exact GlobalTheory.GalStep.main | (intros; apply GlobalTheory.GalStep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero : Moore := by
  first | exact @GlobalTheory.PMon.moore_statement | exact GlobalTheory.PMon.moore_statement | (intros; apply GlobalTheory.PMon.moore_statement <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  first | exact @GlobalTheory.BKExp.muPow_smul_crisVal_integral | exact GlobalTheory.BKExp.muPow_smul_crisVal_integral | (intros; apply GlobalTheory.BKExp.muPow_smul_crisVal_integral <;> assumption)
end

