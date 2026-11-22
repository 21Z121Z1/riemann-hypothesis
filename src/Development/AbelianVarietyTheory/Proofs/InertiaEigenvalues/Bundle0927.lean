import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0009
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ConjHalfSplitInt

theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add, hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem
    rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0SetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admH0_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  first | exact @GlobalTheory.NLink.PowerSmulVanishing.main | exact GlobalTheory.NLink.PowerSmulVanishing.main | (intros; apply GlobalTheory.NLink.PowerSmulVanishing.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parameters_family_const : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  first | exact @GlobalTheory.NLink.admissible_parameters_design_family | exact GlobalTheory.NLink.admissible_parameters_design_family | (intros; apply GlobalTheory.NLink.admissible_parameters_design_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetupStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambient_sub_continuity_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambSub i (X.r i) π (X.dc i) ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π (X.dc i) := by
  first | exact @GlobalTheory.NLink.AmbSub.main | exact GlobalTheory.NLink.AmbSub.main | (intros; apply GlobalTheory.NLink.AmbSub.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
section
noncomputable section

namespace GlobalTheory.CoefExtC

section General

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.AdTh.CoefExt

variable {K : Type} [Field K] {σ : K →+* ℂ} {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n}
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_ext (c' : VV K lam →ₛₗ[σ] W) (hs : Submodule.span ℂ (Set.range c') = ⊤)
    (hli : LinearIndependent ℂ fun j => c' (bVV K lam j)) :
    ∃ c : VV ℂ lam →ₗ[ℂ] W, (∀ v, c (up σ lam v) = c' v) ∧ Function.Bijective c ∧
      ∀ d : VV ℂ lam →ₗ[ℂ] W, (∀ v, d (up σ lam v) = c' v) → d = c := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun j => up σ lam (bVV K lam j)) := by
    intro v _
    obtain ⟨a, rfl⟩ := exists_coord σ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (VVIdx lam) = Module.finrank ℂ (VV ℂ lam) := (Module.finrank_eq_card_basis (bVV ℂ lam)).symm
  let b : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) := basisOfTopLeSpanOfCardEqFinrank _ hsp hcard
  have hb : ∀ j, b j = up σ lam (bVV K lam j) := fun j => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hsp hcard) j
  have hsw : ⊤ ≤ Submodule.span ℂ (Set.range fun j => c' (bVV K lam j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let w : Module.Basis (VVIdx lam) ℂ W := Module.Basis.mk hli hsw
  have hc : ∀ j, (b.equiv w (Equiv.refl _)) (up σ lam (bVV K lam j)) = c' (bVV K lam j) := by
    intro j
    rw [← hb, Module.Basis.equiv_apply]
    exact Module.Basis.mk_apply hli hsw j
  refine ⟨(b.equiv w (Equiv.refl _)).toLinearMap, fun v => ?_, (b.equiv w (Equiv.refl _)).bijective, fun d hd => ?_⟩
  · rw [← (bVV K lam).sum_repr v, up_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smulₛₗ, LinearEquiv.coe_coe, hc]
  · refine b.ext fun j => ?_
    rw [hb, hd, LinearEquiv.coe_coe, hc]

theorem li_basis (c' : VV K lam →ₛₗ[σ] W)
    (h : ∀ (m : ℕ) (b : Fin m → VV K lam), LinearIndependent K b → LinearIndependent ℂ fun j => c' (b j)) :
    LinearIndependent ℂ fun j => c' (bVV K lam j) := by
  let e := Fintype.equivFin (VVIdx lam)
  have h1 := h _ (bVV K lam ∘ e.symm) ((bVV K lam).linearIndependent.comp _ e.symm.injective)
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext j
  simp

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 800000 in

theorem exists_extC_bijective_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨-, h2, h3⟩ := hT.mapL i
  obtain ⟨c, h4, h5, h6⟩ := exists_ext (W := (R.cV i).W) O.c0' (GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3)
    (li_basis (W := (R.cV i).W) O.c0' fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb)
  refine ⟨c, fun v v' hv => ?_, h5, fun d hd => h6 d fun v => hd v _ rfl⟩
  rw [show v' = GlobalTheory.AdTh.CoefExt.up (inC O.c') (lamV D i) v from Subtype.ext hv]
  exact h4 v

end GlobalTheory.CoefExtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRes

section General

variable {D : D7}

theorem locK_conj {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ')
    (τ : ℂ ≃+* ℂ) (hc : ∀ x, ((c' x : Circle) : ℂ) = τ ((c x : Circle) : ℂ)) (P : Pl D.host.E) (k : D.host.Eˣ) :
    ((χ'.locK P k : ℂˣ) : ℂ) = τ ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  rw [← h.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), ← h'.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), hc]

theorem exists_lift (P : Pl D.host.E) (u : (kP P)ˣ) :
    ∃ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a ∧ (u : kP P) = Ideal.Quotient.mk _ a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    rw [this, map_zero] at ha
    exact u.ne_zero ha.symm
  exact ⟨a, Units.mk0 _ h0, rfl, ha.symm⟩

theorem unrAt_of_isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : IsRes χ P 1) : χ.UnrAt P := by
  have key : ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a → a ∉ P.asIdeal → χ.locK P k = 1 := by
    intro a k hk ha
    have := P.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk P.asIdeal a) := by
      let _ := Ideal.Quotient.field P.asIdeal
      exact (Ne.isUnit (fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.1 h0)))
    exact (h a k hu.unit hk rfl).symm
  refine GlobalTheory.EtaConjType.unrAt_of_locK χ P fun u hu => ?_
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer (u : D.host.E) hu.le
  have hd' : d ∉ P.asIdeal := hd
  have hd0 : (d : D.host.E) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    exact hd' (this ▸ P.asIdeal.zero_mem)
  have hn : n ∉ P.asIdeal := by
    rw [← P.valuation_eq_one_iff_notMem (K := D.host.E), ← hnd, map_mul, hu, one_mul]
    exact (P.valuation_eq_one_iff_notMem (K := D.host.E)).2 hd'
  have e1 := key d (Units.mk0 _ hd0) rfl hd'
  have e2 := key n (u * Units.mk0 _ hd0) hnd hn
  rwa [map_mul, e1, mul_one] at e2

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (τ : ℂ ≃+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hχ : ∀ PP ∈ Pg, ∀ x, τ ((χ PP x : ℂˣ) : ℂ) = ((χ PP x : ℂˣ) : ℂ))
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (x) :
    ((levFn β ⟨r, hr, t, 1, Pg, Q', LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ'⟩ x : ℂˣ) : ℂ) =
      τ ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp only [h1, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hχ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => hξ PP hP _

theorem lev_congr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hr : r ≤ V.rank) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (levEnv V β ⟨r, hr, t, 1, Pg, Q', P, χ, ξ'⟩).J = (levEnv V β ⟨r, hr, t, 1, Pg, Q, P, χ, ξ⟩).J := by
  subst hQ
  rfl

theorem levEnv_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V)
    (hk : k ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨k, hk⟩ = levFn β (Lev.flag1L L) (Formalism.UG.bc (Lev.swapAE D) k.1) := rfl

theorem principalLevel_definite_datum_flag_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.flag1L (L.datVt i t) = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, LevelP.triv L.Pg D.R.r ℂ,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem datVt_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    L.datVt i t = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, (LevelP.triv L.Pg D.R.r ℂ).conj,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem lev_datVt {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) {t t' : T0} (h : L.Q t' = L.Q t) :
    (levEnv (Vc D i) (L.βV i) (L.datVt i t')).J = (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J := by
  rw [datVt_eq, datVt_eq]
  exact lev_congr (Vc D i) (L.βV i) (r_le_V i) D.R.t L.Pg h _ _ (L.xiR t) (L.xiR t')

end General

set_option maxHeartbeats 1000000 in

theorem conj_res : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC τ t t' hct
  have hL := hC.lev
  have hloc := locK_conj (hL.xi t) (hL.xi t') τ hct.2
  have h1 : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := by
    intro PP hP x
    obtain ⟨a, k, hk, hx⟩ := exists_lift PP x
    rw [hL.xiR t PP hP a k x hk hx, hL.xiR t' PP (hct.1 ▸ hP) a k x hk hx]
    exact hloc PP k
  refine ⟨h1, fun PP hP h => ?_, fun P => hloc P _, fun i hτ => ⟨?_, fun k hk hk' => ?_⟩⟩
  · exact (hL.Q_ram t PP).2 (Or.inl hP) (unrAt_of_isRes_one (h ▸ hL.xiR t PP hP))
  · exact lev_datVt R.toLevCh i hct.1
  · rw [levEnv_chi, levEnv_chi, principalLevel_definite_datum_flag_eq, principalLevel_definite_datum_flag_eq]
    exact levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hct.1 τ (R.chi ((i : ℕ) + 1)) (R.xiR t) (R.xiR t') hτ.chi h1 _

end GlobalTheory.ConjRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverCharacterTrivialOnLevelDeterminants
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverXiDet

theorem natM_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
  rw [← l.prod] at h
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h

theorem natM_mem_of_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l l₂ : Level H)
    (I P : Ideal (𝓞 E)) (h : l₂.Mb = l.Mb * I) (hI : I ≤ P) : ((l₂.M : ℕ) : 𝓞 E) ∈ P := by
  have h1 := natM_mem_Mb l₂
  rw [h] at h1
  exact hI (Ideal.mul_le_right (I := l.Mb) (J := I) h1)

end GlobalTheory.CoverXiDet

namespace GlobalTheory.CoverXiDet

set_option maxHeartbeats 4000000 in

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hM t u _ hw
  have hL := hC.lev
  have hN : ∀ PP ∈ R.Q (tup t), (((M.dδ t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    natM_mem_of_half _ _ _ _ ((hM.cov t).1).2.2.2.1 ((hM.tuple t).half.2.1 PP hPP)
  obtain ⟨xi', hxi1, hxi2, -, -⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi (tup t))
    (hL.xi_fin (tup t)).choose (hL.xi_fin (tup t)).choose_spec.1 (hL.xi_fin (tup t)).choose_spec.2 (hL.xi_triv (tup t))
    (hL.xi_tame (tup t))
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Wc D i) u
  have e1 := (hM.tuple t).xi u x hx
  have e2 := hxi1 u x hx
  have e3 : xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    refine hxi2 _ (M.dδ t).l₂.odd (GlobalTheory.TupleCover.unrAt_of_not_mem R hL (tup t) _ hN) u ?_
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, (GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers D).symm ▸ hw1, hw2⟩
  apply Units.ext
  rw [e1, ← e2, e3]

end GlobalTheory.CoverXiDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadingsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverSections_linearIndependent_adelicReadings : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) → LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => C.rd a (f i)) := by
  first | exact @GlobalTheory.CoverIndep.cover_rd_linearIndependent | exact GlobalTheory.CoverIndep.cover_rd_linearIndependent | (intros; apply GlobalTheory.CoverIndep.cover_rd_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRelation

theorem relation_conj {K C X : Type} [Field K] [AddCommGroup C] [Module K C] (σ : K →+* ℂ) (Φ : C →ₛₗ[σ] (X → ℂ))
    (hΦ : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun k => Φ (b k))
    (τ : ℂ ≃+* ℂ) (hτ : ∀ x, τ (σ x) = σ x) {n : ℕ} (a : Fin n → ℂ) (f : Fin n → C)
    (h : ∀ g, (0 : ℂ) = ∑ k, a k * Φ (f k) g) (g : X) : (0 : ℂ) = ∑ k, τ (a k) * Φ (f k) g := by
  let S := Submodule.span K (Set.range f)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range f)
  let b := Module.finBasis K S
  have hb := hΦ _ (fun l => (b l : C)) (b.linearIndependent.map' S.subtype (Submodule.ker_subtype _))
  let c : Fin n → Fin (Module.finrank K S) → K := fun k l => b.repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩ l
  have hf : ∀ k, f k = ∑ l, c k l • (b l : C) := fun k => by
    have h1 := congrArg S.subtype (b.sum_repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩)
    rw [map_sum] at h1
    exact h1.symm
  have key : ∀ (a' : Fin n → ℂ) (x : X), ∑ k, a' k * Φ (f k) x = ∑ l, (∑ k, a' k * σ (c k l)) * Φ (b l) x := by
    intro a' x
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h0 : ∀ l, ∑ k, a k * σ (c k l) = 0 := by
    refine Fintype.linearIndependent_iff.1 hb _ ?_
    funext x
    rw [Finset.sum_apply]
    exact ((h x).trans (key a x)).symm
  rw [key]
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  have h1 := congrArg τ (h0 l)
  simp only [map_sum, map_mul, hτ, map_zero] at h1
  rw [h1, zero_mul]

theorem exists_semilinear {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    ∃ Φ : T.R j →ₛₗ[σ] (GA D W → ℂ), (∀ f, Φ f = phiC T hV a f) ∧ ∀ f g, Φ f g =
      ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * adel W (castDict hV (T.dict j σ))
        (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) g := by
  subst hV
  exact ⟨(((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) • adel (T.V j σ) (T.dict j σ)
    (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))).comp (rdU (T.U j σ)), fun _ => rfl, fun _ _ => rfl⟩

set_option maxHeartbeats 1000000 in

theorem expands_zero_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hfw i Tp tup M _ τ hτ n a f h
  obtain ⟨fw⟩ := hfw
  have hσ : GoodEmb T.Q.c M.s0 := T.toCore.good_σ₀
  have hex := exists_semilinear T M.hV (wtA (κ i))
  obtain ⟨Φ, h1, h2⟩ := hex
  have hI := GlobalTheory.PhiIndep.phiC_indep D T κ fw.laws i M.s0 hσ M.hV
  intro g
  have hr := relation_conj M.s0 (Φ.comp (T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
    (fun m b hb => (funext fun k => h1 (b k : T.R ((i : ℕ) + 1))).symm ▸ hI m b hb) τ hτ a f
    (fun x => (h x).trans (Finset.sum_congr rfl fun k _ => congrArg (a k * ·) (h2 _ x).symm)) g
  exact hr.trans (Finset.sum_congr rfl fun k _ => congrArg (τ (a k) * ·) (h2 _ g))

end GlobalTheory.ConjRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocyclesLocallyConstantKilledByUniformiserPow
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
theorem _root_.GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (lam : ↥(OL C.LL)), Irreducible lam → GoodR D.nd i r → TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
    ∃ a : ℕ, (fun g => liftQ C.le k (z g)) ∈ divisibleCocycles (latC C (locOC C M)) ∧ ∀ g, lam ^ a • liftQ C.le k (z g) = 0 := by
  intro D i r w hw C lam hlam hGood _ k M z hz
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have htop : IsTopologicalRing ↥C.LL.1 := hG.2.2.2.1
  have hopen := hG.2.2.2.2
  have h1 := UpperTheory.KN.continuous_localCoefficientRep_twist D i r w hw C hGood
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C M z hz
  have h3 := @UpperTheory.KN.exists_cocycle_torsion_of_hasPres (Br.G D.nbr i w hw) ↥(OL C.LL) ↥C.LL.1 _ _ _ hdom hdvr _ _ htop _ hfr Subtype.val_injective lam _ _ _
    (fun x => locOC C (rTwO D.nd i r x)) (locOC C M) (fun g => liftQ C.le k (z g)) hlam hopen h1
  exact h3 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfLabelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_zero_of_labels : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → DepthZ D := by
  first | exact @GlobalTheory.DepthZeroTame.main | exact GlobalTheory.DepthZeroTame.main | (intros; apply GlobalTheory.DepthZeroTame.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  first | exact @GlobalTheory.UseFive.objects_globalStep_gen | exact GlobalTheory.UseFive.objects_globalStep_gen | (intros; apply GlobalTheory.UseFive.objects_globalStep_gen <;> assumption)
end

