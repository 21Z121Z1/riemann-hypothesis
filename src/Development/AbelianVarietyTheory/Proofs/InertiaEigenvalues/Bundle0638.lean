import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrisCoord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : Type} [CommRing B] [Algebra F B] {d : ℕ}

def crd (bV : Module.Basis (Fin d) F V) (r : Fin d) : V ⊗[F] B →ₗ[F] B :=
  (TensorProduct.lid F B).toLinearMap ∘ₗ TensorProduct.map (bV.coord r) LinearMap.id

theorem crd_tmul (bV : Module.Basis (Fin d) F V) (r : Fin d) (v : V) (x : B) :
    crd bV r (v ⊗ₜ[F] x) = bV.coord r v • x := by
  simp [crd]

theorem crd_mulLeft (bV : Module.Basis (Fin d) F V) (r : Fin d) (β : B) (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[F] V) (LinearMap.mulLeft F β) z) =
      β * crd bV r z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [crd_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem crd_map (bV : Module.Basis (Fin d) F V) (r : Fin d) (f : V →ₗ[F] V) (σ : B →ₗ[F] B)
    (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map f σ z) =
      ∑ s, LinearMap.toMatrix bV bV f r s • σ (crd bV s z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    have h := congrFun (LinearMap.toMatrix_mulVec_repr bV bV f v) r
    simp only [Matrix.mulVec, dotProduct] at h
    simp only [AlgebraTensorModule.map_tmul, crd_tmul, Module.Basis.coord_apply, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← h]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]

theorem crd_basis (bV : Module.Basis (Fin d) F V) (r j : Fin d) :
    crd bV r ((bV j) ⊗ₜ[F] (1 : B)) = if r = j then 1 else 0 := by
  rw [crd_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : r = j
  · subst h; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm h), if_neg h, zero_smul]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V] {d : ℕ}

theorem linIndep_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) :
    LinearIndependent ℚ_[l] (fun i => (b i : V)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
  exact b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)

theorem sum_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) :
    (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • (b i : V) := by
  have h := congrArg T.subtype (b.sum_repr w)
  rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  simp only [algebraMap_smul]
  exact h.symm

theorem span_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
  rw [← hT]
  refine Submodule.span_le.mpr fun x hx => ?_
  rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, sum_lat T b]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def bVL (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (linIndep_lat T b) (span_lat T hT b)

theorem bVL_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : bVL T hT b i = (b i : V) := by
  simp [bVL]

theorem repr_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) (r : Fin d) :
    (bVL T hT b).repr (w : V) r = algebraMap ℤ_[l] ℚ_[l] (b.repr w r) := by
  have h : (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • bVL T hT b i := by
    simp only [bVL_apply]; exact sum_lat T b w
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

theorem toMatrix_lat {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] G V}
    (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] L.T) (g : G) (r s : Fin d) :
    LinearMap.toMatrix (bVL L.T L.span b) (bVL L.T L.span b) (ρ g) r s =
      algebraMap ℤ_[l] ℚ_[l] (LinearMap.toMatrix b b (actT L g) r s) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, bVL_apply, ← repr_lat L.T L.span b]
  rfl

theorem lattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hC d b j
  obtain ⟨m, β, δ, hδ, hy⟩ :=
    GlobalTheory.T.dcris_span_tensorBcris_rat l P AI T K V ρ hC ((bVL L.T L.span b j) ⊗ₜ[ℚ_[l]] (1 : P.R.B))
  refine ⟨m, fun i => T.eB (β i), fun i r => T.eB (crd (bVL L.T L.span b) r (δ i)), ?_, ?_⟩
  · intro i g
    have hinv : actVB (P.PD K) ρ g (δ i) = δ i := by
      have h := hδ i
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at h
      exact h g
    funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hinv
    beta_reduce
    rw [← key, actVB, crd_map]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [toMatrix_lat, Algebra.smul_def, map_mul, PadicInt.algebraMap_apply, T.zB]
    congr 1
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe]
    rw [← T.actB]
    congr 1
    exact (P.PD_actB K g _).symm
  · funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hy
    simp only [map_sum, crd_mulLeft, crd_basis, map_mul] at key
    beta_reduce
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← key]
    by_cases h : r = j
    · subst h; simp
    · simp [h]

end GlobalTheory.CrisCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.DualTwistCrys

theorem crys_bridge (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hR : GoodR D.nd i r) (hCr : SumRepresentations.At.G2 D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
  ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hR x).1).1.1 (((hCr w hw).1 h0 h1 x).1)

theorem crys_chi (D : D7) (i : D.nd.Loc) (hChi : GlobalTheory.PtCore.ChiOneE D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := hChi w hw C.LL C.le

theorem card_emb (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
  have := D.nd.lPrime i
  have := C.LL.2
  have := (D.nbr i w hw).Kw.2
  have h2 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw C.LL (fun τ y => C.le
    ((D.nbr i w hw).LL_split τ y)) inferInstance).2
  rw [Nat.card_eq_fintype_card, h2]

theorem twist_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) := by
  have := D.nd.lPrime i
  have := C.LL.2
  refine (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _)
    (D.nbr i w hw).Kw C.LL _ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) _
    (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
    ⟨LinearEquiv.refl _ _, fun g v => ?_⟩ hchi hcC).1
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, GlobalTheory.TateDualCrys.matRep_apply,
    GlobalTheory.TateDualCrys.matRep_apply]
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hcw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ hcw

theorem dual_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (htw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact (GlobalTheory.TateDualCrys.tateDual (D.locT _) (D.nbr i w hw).Kw C.LL (card_emb D i w hw C) _ _
    (GlobalTheory.TateDualCrys.loc_rDuO D i w hw C.LL C.le r x) htw).1

theorem tw_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  rw [← GlobalTheory.AmbientDual.twist_locC]
  exact twist_crys D i r w hw C x hchi hcC

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → SumRepresentations.At.G2 D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → GlobalTheory.PtCore.ChiOneE D i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) :=
  fun _ D i r hR hCr h0 h1 hChi w hw C x =>
    dual_crys D i r w hw C x (tw_crys D i r w hw C x (crys_chi D i hChi w hw C)
      (crys_coef D i r w hw C x (crys_bridge D i r hR hCr h0 h1 w hw x)))

end GlobalTheory.DualTwistCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompare
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoOrth

open GlobalTheory.BKOrth

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem pairT_filV_right (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : ℤ) (v : V) (z : V' ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V') a) :
    pairT BdR P (v ⊗ₜ[Qp] (1 : BdR)) z ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add]; exact add_mem hy hy'
  | tmul v' f =>
    rw [AlgebraTensorModule.map_tmul, pairT_tmul, one_mul]
    exact ⟨P v v' ⊗ₜ[Qp] f, rfl⟩

theorem actVB_one (ρ : Representation LL G V) (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actVB_tmul]

end Gen

theorem cocycle_inv {G : Type} [Group G] {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) :
    ρ g (c g⁻¹) = - c g := by
  have h1 : c 1 = 0 := by simpa using hc 1 1
  have := hc g g⁻¹
  rw [mul_inv_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem goodO_Zl (l : ℕ) [Fact l.Prime] : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (PadicInt.isOpenEmbedding_coe (p := l)).isOpen_range

set_option maxHeartbeats 1600000 in

theorem orth_of_cont (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V']
    [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V')
    (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hρ' : ∀ y, Continuous fun g => ρ' g y)
    (hdR : IsDR (P.PD K) ρ') (hD : IsDual1 (P.PD K) ρ ρ' m)
    (hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]))
    (c : ↥(GK K) → V) (hc : c ∈ geometricCocycles (P.PD K) ρ) (a : ↥(GK K) → V')
    (ha : a ∈ crystallineCocycles (P.PD K) ρ') : CobL (P.PD K) (cupL ρ' m c a) := by
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hcz, b, hb⟩ := hc
  obtain ⟨haz, β, hβφ, hβ⟩ := ha
  obtain ⟨-, d, hd, hd'⟩ :=
    GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      { V := V', ρ := ρ', cont := hρ' } hdR a β hβ
  have hfixd : ∀ g, actVdR (P.PD K) ρ' g d = d := fun g => by
    have := (Submodule.mem_iInf _).1 hd g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K ℚ_[l] ℚ_[l]
  obtain ⟨we, w0, hw0, hweφ, hweι⟩ := hsurj 0 (pairT P.R.BdR m b d)
  have hweφ' : φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = we := (sub_eq_zero.1 hweφ).symm
  let F : ↥(GK K) → ℚ_[l] ⊗[ℚ_[l]] P.R.B := fun h =>
    (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h we - we) -
      pairT P.R.B m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' h β)
  have hFφ : ∀ h, φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) = F h := fun h => by
    have e1 : φVB (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
      simp [φVB]
    simp only [F, map_sub, pairT_φVB, e1, GlobalTheory.CobCrisLift.φVB_act, hβφ, hweφ']
  have hFι : ∀ h, ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) ∈
      FilV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) 0 := fun h => by
    have e1 : ιV (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
      simp [ιV]
    have e2 : pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) (actVdR (P.PD K) ρ' h d) =
        actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h (pairT P.R.BdR m b d) -
          pairT P.R.BdR m b d := by
      rw [hb h, map_sub, LinearMap.sub_apply, ← pairT_actVdR (P.PD K) ρ ρ' m hD.1 h b d, hfixd h]
    have hι1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = pairT P.R.BdR m b d + w0 :=
      sub_eq_iff_eq_add.1 hweι
    have s1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) =
        (actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h w0 - w0) -
          pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR))
            (actVdR (P.PD K) ρ' h (ιV (P.PD K) (LL := ℚ_[l]) (V := V') β - d)) := by
      simp only [F, map_sub, pairT_ιV, e1, GlobalTheory.CobCrisLift.ιV_act, hι1, map_add, e2]
      abel
    rw [s1]
    exact sub_mem (sub_mem (actVdR_filV (P.PD K) _ 0 h w0 hw0) hw0)
      (pairT_filV_right (P.PD K) m 0 (c h) _ (actVdR_filV (P.PD K) ρ' 0 h _ hd'))
  have hF : ∀ h, ∃ x : ℚ_[l], F h = x ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun h => hker (F h) (hFφ h) (hFι h)
  choose f hf using hF
  let bas := Module.finBasis ℚ_[l] V
  let γ : Fin (finrank ℚ_[l] V) → ↥(GK K) → ℚ_[l] := fun i g => bas.coord i (c g)
  have hγ : ∀ i, Continuous (γ i) := fun i =>
    (IsModuleTopology.continuous_of_linearMap (bas.coord i)).comp hcz.1
  let k : ↥(GK K) → ℚ_[l] := fun h => charRep (cycLL (P.PD K) ℚ_[l]) h (f h⁻¹)
  have hsum : ∀ g, k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      ∑ i, γ i g • pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β +
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (-we) - -we) := by
    intro g
    have ec : c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, γ i g • (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
      conv_lhs => rw [← bas.sum_repr (c g)]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul']
      rfl
    have ek : k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F g⁻¹) := by
      rw [hf g⁻¹, actVB_tmul, map_one]
    have e3 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (pairT P.R.B m (c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g⁻¹ β)) =
        -pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β := by
      rw [← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, ← actVB_mul, mul_inv_cancel, actVB_one, actVB_tmul,
        map_one, cocycle_inv ρ c hcz.2 g, neg_tmul, map_neg, LinearMap.neg_apply]
    have e4 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g⁻¹ we) = we := by
      rw [← actVB_mul, mul_inv_cancel, actVB_one]
    rw [ek]
    simp only [F, map_sub, e3, e4, map_neg, ec, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply]
    abel
  have hk : Continuous k :=
    GlobalTheory.FundCont.contCore_tied l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      (charGRep (Qp := ℚ_[l]) (O := ℤ_[l]) (cycLL (P.PD K) ℚ_[l]) hχ) _
      (fun i => pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β) γ hγ (-we) k hsum
  have hfk : f = fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * k g⁻¹ := by
    funext g
    simp only [k, charRep_apply, inv_inv]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
  have hcont : Continuous f := by
    rw [hfk]
    exact hχ.mul (hk.comp continuous_inv)
  refine ⟨f, hcont, ?_⟩
  funext ⟨g, h⟩
  have hcup : cupL ρ' m c a (g, h) = m (c g) (ρ' g (a h)) := rfl
  rw [hcup]
  apply tmul_one_injective (P.PD K) (LL := ℚ_[l])
  beta_reduce
  have hd1 : ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h) =
      charRep (cycLL (P.PD K) ℚ_[l]) g (f h) - f (g * h) + f g := rfl
  have hact : (charRep (cycLL (P.PD K) ℚ_[l]) g (f h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [actVB_tmul, map_one]
  have hch : actVB (P.PD K) ρ g (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [actVB_tmul, map_one]
  have hcoc : c (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) + ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [hcz.2 g h, add_tmul]
  have hrhs : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    have e : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g (a h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) := by
      rw [actVB_tmul, map_one, pairT_tmul, mul_one]
    rw [e, hβ h, map_sub, map_sub]
  have main : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    simp only [F, map_sub, actVB_mul, hcoc, map_add, LinearMap.add_apply,
      ← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, hch]
    abel
  calc (ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
      = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          f (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) + f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
        rw [hd1, tmul_one_sub_add, hact]
    _ = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g := by
        rw [hf h, hf (g * h), hf g]
    _ = _ := main
    _ = _ := hrhs.symm

theorem hyodo_orth : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hρ hρ' hdR hD c hc a ha
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ : ∃ v', m v v' ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hD.2.1 v h)
    have hm : Continuous fun p : V × V' => m p.1 p.2 :=
      IsModuleTopology.continuous_bilinear_of_finite_left m
    have hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      have e : (fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) =
          fun g => m (ρ g v) (ρ' g v') * (m v v')⁻¹ := by
        funext g
        rw [hD.1, mul_assoc, mul_inv_cancel₀ hv', mul_one]
      rw [e]
      exact (hm.comp ((hρ v).prodMk (hρ' v'))).mul continuous_const
    exact orth_of_cont l P AI hT K V ρ V' ρ' m hρ' hdR hD hχ c hc a ha
  · push_neg at hV
    refine ⟨0, continuous_const, funext fun x => ?_⟩
    simp [cupL, hV (c x.1), ReciprocityTheory.Def.d1]

end GlobalTheory.HyodoOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPairStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  first | exact @GlobalTheory.FundDel.connecting_cocycle | exact GlobalTheory.FundDel.connecting_cocycle | (intros; apply GlobalTheory.FundDel.connecting_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_periods_disc_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  first | exact @GlobalTheory.BSP.exists_bounded_periods | exact GlobalTheory.BSP.exists_bounded_periods | (intros; apply GlobalTheory.BSP.exists_bounded_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltrationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  first | exact @GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | exact GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | (intros; apply GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWittStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusMatrix_crystallineModule_over_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  first | exact @GlobalTheory.SeedF.frob_matrix | exact GlobalTheory.SeedF.frob_matrix | (intros; apply GlobalTheory.SeedF.frob_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClassStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusPotential_cocycle_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  first | exact @GlobalTheory.GalPot.potential_class | exact GlobalTheory.GalPot.potential_class | (intros; apply GlobalTheory.GalPot.potential_class <;> assumption)
end

