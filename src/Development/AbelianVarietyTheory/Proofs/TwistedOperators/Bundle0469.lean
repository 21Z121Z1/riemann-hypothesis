import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0371
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPointCarryingFrameLat
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FramePointMove

open scoped Matrix

theorem conj_maps_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, (J * x * J⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, x.1 *ᵥ w ∈ P := by
  have hinj : Function.Injective J.1.mulVec := fun a b h => by
    have := congrArg (fun z => (J⁻¹).1 *ᵥ z) h
    simpa [Matrix.mulVec_mulVec] using this
  have mem : ∀ z, J.1 *ᵥ z ∈ Q ↔ z ∈ P := fun z => by
    rw [← hJ, hinj.mem_set_image]
  have e : ∀ w, (J * x * J⁻¹).1 *ᵥ (J.1 *ᵥ w) = J.1 *ᵥ (x.1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp [Matrix.mul_assoc]
  constructor
  · intro h w hw
    have := h _ ((mem w).2 hw)
    rwa [e, mem] at this
  · intro h y hy
    rw [← hJ] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [e, mem]
    exact h w hw

theorem conj_maps_inv_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, ((J * x * J⁻¹)⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, (x⁻¹).1 *ᵥ w ∈ P := by
  have hinv : (J * x * J⁻¹)⁻¹ = J * x⁻¹ * J⁻¹ := by group
  rw [hinv]
  exact conj_maps_iff J x⁻¹ hJ

set_option maxHeartbeats 800000 in

theorem exists_point_carrying_frameLat : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ a : GfC V, GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val ∧ ∀ g : GfC V, finE V ((a * g * a⁻¹ : GfC V) : GA D V) ∈ St β ↔ ∀ v, finLoc V v g ∈ Kv V v := by
  intro D V β Λ N hβ
  obtain ⟨β₀, -, hβ₀⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D V
  obtain ⟨j, hj, -⟩ := GlobalTheory.FinAdIdent.exists_latIsom V V rfl (frameLat V) Λ β₀ β 1 N hβ₀ hβ ∅
    (fun _ h => absurd h (Set.notMem_empty _))
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  let J : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) := ⟨j, j', h1, h2⟩
  have hJ : J ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := hj.1.2
  obtain ⟨k, hk, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V J hJ
  refine ⟨⟨k, hk⟩, ?_, fun g => ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V k).val
    rw [e]
    exact hj
  · have hg : finE V ((⟨k, hk⟩ * g * ⟨k, hk⟩⁻¹ : GfC V) : GA D V) = J * finE V (g : GA D V) * J⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, e]
    have hJP : J.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) (frameLat V) : Set _) =
        (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) := hj.2
    rw [hg, GlobalTheory.LevSplit.mem_St_iff β Λ hβ.1]
    have hs := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β₀ (frameLat V) hβ₀.1 (g : GA D V)
    rw [GlobalTheory.LevSplit.mem_St_iff β₀ (frameLat V) hβ₀.1] at hs
    refine Iff.trans ?_ hs
    exact and_congr (conj_maps_iff J _ hJP) (conj_maps_inv_iff J _ hJP)

end GlobalTheory.FramePointMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalApproxFinitePointVacuumLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinApprox

variable {D : D7}

def finRat (D : D7) : D.host.E →+ AE D := TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 1)

theorem finRat_apply (a : D.host.E) : finRat D a = pairA D.host.F 0 1 ⊗ₜ[D.host.F] a := rfl

theorem finRat_eq (a : D.host.E) : incA D a - pairA D.host.F 1 0 ⊗ₜ[D.host.F] a = finRat D a := by
  have h1 : (1 : AF D.host.F) = pairA D.host.F 1 0 + pairA D.host.F 0 1 :=
    Prod.ext (add_zero (1 : Ainf D.host.F)).symm (zero_add (1 : Af D.host.F)).symm
  rw [finRat_apply]
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] a - _ = _
  rw [h1, TensorProduct.add_tmul, add_sub_cancel_left]

private theorem infPart_tmul' (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem infPart_finRat (a : D.host.E) : infPart D (finRat D a) = 0 := by
  rw [finRat_apply, infPart_tmul']
  have h0 : fstA D.host.F (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (w : AE D) :
    w = ∑ i, (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr w i ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).sum_repr w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fstA_basis_repr_eq_zero_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) (i : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i) = 0 := by
  have h1 : infPart D z = ∑ j, fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z j) •
      Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E) j := by
    conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [infPart_tmul', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 := congrArg
    (fun v => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr v i) h1
  simp only [hz, map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_sum_self] at h2
  exact h2.symm

private theorem eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) :
    z = ∑ i, pairA D.host.F 0 (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Prod.ext (fstA_basis_repr_eq_zero_of_infPart_eq_zero hz i) rfl

theorem mem_closure_finRat {z : AE D} (hz : infPart D z = 0) : z ∈ closure (Set.range (finRat D)) := by
  have hd : DenseRange (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) =>
      ⇑(algebraMap D.host.F (Af D.host.F))) :=
    DenseRange.piMap fun _ => AdeleCharTwist.denseRange_fin
  have hc : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
    refine continuous_finset_sum _ fun i _ => ?_
    have h1 : Continuous fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
      have he : (fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) =
          fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact Continuous.smul (M := AF D.host.F) (X := AE D) continuous_id continuous_const
    have h2 : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => pairA D.host.F 0 (y i) := by
      show Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => ((0 : Ainf D.host.F), y i)
      exact continuous_const.prodMk (continuous_apply i)
    exact h1.comp h2
  have hm : Set.MapsTo (fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i)
      (Set.range (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) => ⇑(algebraMap D.host.F (Af D.host.F))))
      (Set.range (finRat D)) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨∑ i, q i • Module.finBasis D.host.F D.host.E i, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRat_apply, ← TensorProduct.smul_tmul]
    congr 1
    exact Prod.ext (smul_zero (q i)) ((Algebra.smul_def (q i) (1 : Af D.host.F)).trans (mul_one _))
  have hz' := map_mem_closure hc (hd fun i => sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) hm
  rw [eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero hz]
  exact hz'

theorem mem_closure_mat {m n : ℕ} {y : Mx D m n} (hy : y.map (infPart D) = 0) :
    y ∈ closure (Set.range fun ℓ : Matrix (Fin m) (Fin n) D.host.E => (ℓ.map (finRat D) : Mx D m n)) := by
  have h1 : ∀ i j, y i j ∈ closure (Set.range (finRat D)) := fun i j =>
    mem_closure_finRat (by simpa using congrFun (congrFun hy i) j)
  have h2 : (y : Fin m → Fin n → AE D) ∈
      closure (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => Set.range (finRat D)) := by
    refine mem_closure_pi.mpr fun i _ => ?_
    refine mem_closure_pi.mpr fun j _ => ?_
    exact h1 i j
  refine closure_mono ?_ h2
  intro x hx
  have hx' : ∀ i j, ∃ a, finRat D a = x i j := fun i j => hx i (Set.mem_univ i) j (Set.mem_univ j)
  choose ℓ hℓ using hx'
  exact ⟨Matrix.of ℓ, by ext i j; exact hℓ i j⟩

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]

private theorem continuous_actO_one {S T : HSp D} (h : GA D T) : Continuous (actO S T 1 h) := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold actO
  fun_prop

theorem exists_approx {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (g : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    ∃ (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), w.map (infPart D) = 0 ∧ heisO ψ S T w f = f ∧
      x = actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) + w := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hy : (actO S T 1 g x).map (infPart D) = 0 := actO_fin 1 g hx
  have hVo : IsOpen {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} :=
    hUo.preimage ((continuous_actO_one (S := S) g⁻¹).comp (continuous_const.sub continuous_id))
  have h0 : actO S T 1 g⁻¹ 0 = 0 := by
    have h00 := GlobalTheory.HeckeVacuum.act_sub g⁻¹ (0 : WO S T) 0
    rwa [sub_self, sub_self] at h00
  have hyV : actO S T 1 g x ∈ {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} := by
    show actO S T 1 g⁻¹ (actO S T 1 g x - actO S T 1 g x) ∈ U
    rw [sub_self, h0]
    exact U.zero_mem
  obtain ⟨_, hvV, ℓ, rfl⟩ := mem_closure_iff.mp (mem_closure_mat (m := T.rank) (n := S.rank) hy) _ hVo hyV
  have hrat : ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ = (ℓ.map (finRat D) : WO S T) := by
    ext i j
    exact finRat_eq (ℓ i j)
  have key : actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) =
      actO S T 1 g⁻¹ (ℓ.map (finRat D)) := congrArg _ hrat
  have hw : (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))).map (infPart D) = 0 := by
    refine actO_fin 1 g⁻¹ ?_
    ext i j
    have hij : infPart D (actO S T 1 g x i j) = 0 := by simpa using congrFun (congrFun hy i) j
    simp [hij, infPart_finRat]
  refine ⟨ℓ, actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D)), hw,
    hU (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))) hvV hw, ?_⟩
  rw [key, GlobalTheory.HeckeVacuum.act_sub, add_sub_cancel, ← GlobalTheory.HeckeVacuum.act_mul, inv_mul_cancel,
    GlobalTheory.HeckeVacuum.act_one]

theorem exists_rat_approx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  intro D G _ _ Pl0 T0 A T _ R _ _ hP i g x hx
  exact exists_approx (hP.vP i A.μ0).1.2.theta g hx

end GlobalTheory.FinApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRelOfLocalMatching
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareRel

section Rel

variable {P Q Pr : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pr] [Module ℂ Pr]

def relOf (q : P →ₗ[ℂ] Pr) (q' : Q →ₗ[ℂ] Pr) : Submodule ℂ (P × Q) :=
  LinearMap.eqLocus (q ∘ₗ LinearMap.fst ℂ P Q) (q' ∘ₗ LinearMap.snd ℂ P Q)

theorem mem_relOf {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} {x : P × Q} : x ∈ relOf q q' ↔ q x.1 = q' x.2 := Iff.rfl

theorem relOf_fst {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq' : Function.Surjective q') (a : P) : ∃ b, (a, b) ∈ relOf q q' := by
  obtain ⟨b, hb⟩ := hq' (q a)
  exact ⟨b, hb.symm⟩

theorem relOf_snd {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) (b : Q) : ∃ a, (a, b) ∈ relOf q q' := by
  obtain ⟨a, ha⟩ := hq (q' b)
  exact ⟨a, ha⟩

theorem relOf_ne_top [Nontrivial Pr] {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) : relOf q q' ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
  obtain ⟨a, rfl⟩ := hq y
  have h1 : (a, (0 : Q)) ∈ relOf q q' := h ▸ Submodule.mem_top
  rw [mem_relOf, map_zero] at h1
  exact hy h1

end Rel

section Pol

variable {σ₁ σ₂ ν : Type} (e : σ₁ ⊕ σ₂ ≃ ν)

def polTens : MvPolynomial σ₁ ℂ ⊗[ℂ] MvPolynomial σ₂ ℂ ≃ₗ[ℂ] MvPolynomial ν ℂ :=
  ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)).equiv
    (MvPolynomial.basisMonomials ν ℂ) (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr e).toEquiv)

theorem finsupp_sum_eq (m : σ₁ →₀ ℕ) (n : σ₂ →₀ ℕ) :
    Finsupp.domCongr e (Finsupp.sumElim m n) = m.mapDomain (e ∘ Sum.inl) + n.mapDomain (e ∘ Sum.inr) := by
  ext x
  obtain ⟨s, rfl⟩ := e.surjective x
  have h1 : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have h2 : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  rcases s with s | s
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inl]
    rw [show e (Sum.inl s) = (e ∘ Sum.inl) s from rfl, Finsupp.mapDomain_apply h1, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu).symm
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inr]
    rw [show e (Sum.inr s) = (e ∘ Sum.inr) s from rfl, Finsupp.mapDomain_apply h2, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu)

theorem polTens_tmul (p₁ : MvPolynomial σ₁ ℂ) (p₂ : MvPolynomial σ₂ ℂ) :
    polTens e (p₁ ⊗ₜ p₂) = MvPolynomial.rename (e ∘ Sum.inl) p₁ * MvPolynomial.rename (e ∘ Sum.inr) p₂ := by
  have key : (TensorProduct.mk ℂ _ _).compr₂ (polTens e).toLinearMap =
      (LinearMap.mul ℂ (MvPolynomial ν ℂ)).compl₁₂ (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inl)).toLinearMap
        (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inr)).toLinearMap := by
    refine (MvPolynomial.basisMonomials σ₁ ℂ).ext fun m => (MvPolynomial.basisMonomials σ₂ ℂ).ext fun n => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    have h : (MvPolynomial.monomial m (1 : ℂ)) ⊗ₜ[ℂ] (MvPolynomial.monomial n (1 : ℂ)) =
        ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)) (m, n) := by
      rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.coe_basisMonomials]
    rw [h, polTens]
    erw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one,
      Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    rw [finsupp_sum_eq]
  exact LinearMap.congr_fun₂ key p₁ p₂

end Pol

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

section Route

variable {D : D7} {a b c d b' : ℕ}

def routeVar (en : Fin a ⊕ Fin c ≃ Fin d) (eb : Fin b ≃ Fin b') : FVar D a b ⊕ FVar D b c ≃ FVar D d b' where
  toFun := Sum.elim (fun v => (v.1, en (.inl v.2.1), eb v.2.2)) (fun v => (v.1, en (.inr v.2.2), eb v.2.1))
  invFun w := Sum.elim (fun x => Sum.inl (w.1, x, eb.symm w.2.2)) (fun z => Sum.inr (w.1, eb.symm w.2.2, z)) (en.symm w.2.1)
  left_inv := by rintro (⟨τ, x, y⟩ | ⟨τ, y, z⟩) <;> simp
  right_inv := by
    rintro ⟨τ, k, y⟩
    rcases h : en.symm k with x | z
    · obtain rfl := en.symm_apply_eq.1 h
      simp
    · obtain rfl := en.symm_apply_eq.1 h
      simp

def polRoute (en : Fin a ⊕ Fin c ≃ Fin d) (eb : Fin b ≃ Fin b') : PolF D a b ⊗[ℂ] PolF D b c ≃ₗ[ℂ] PolF D d b' :=
  polTens (routeVar en eb)

end Route

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : ℕ) {d b' b₁ : ℕ}

def iotaBig (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb : Fin (G.V (.grid (i + 1) (j + 1))).rank ≃ Fin b') :
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ≃ₗ[ℂ] PolF D d b' :=
  polRoute en eb

def iotaSmall (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb₁ : Fin (G.V (.grid i j)).rank ≃ Fin b₁) :
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) ≃ₗ[ℂ] PolF D d b₁ :=
  polRoute en eb₁

def squareRel (en : Fin (G.V (.grid i (j + 1))).rank ⊕ Fin (G.V (.grid (i + 1) j)).rank ≃ Fin d)
    (eb : Fin (G.V (.grid (i + 1) (j + 1))).rank ≃ Fin b') (eb₁ : Fin (G.V (.grid i j)).rank ≃ Fin b₁) {Pr : Type*}
    [AddCommGroup Pr] [Module ℂ Pr] (q : PolF D d b' →ₗ[ℂ] Pr) (q' : PolF D d b₁ →ₗ[ℂ] Pr) :
    Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :=
  relOf (q ∘ₗ (iotaBig G i j en eb).toLinearMap) (q' ∘ₗ (iotaSmall G i j en eb₁).toLinearMap)

theorem hasInfExp_alpha {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (τ : D.what₂.Tau) {a : ℚ}
    (h : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ a) : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j) τ a := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := id h
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨n', hn', ho'⟩ := hL.xi_fin t'
  have h0 := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  have h0' := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t') hn' ho' τ
  have hK : ∀ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G s i j = (L.mu0 (j + 1) * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) * L.xi s := fun s => by
    show L.mu0 (j + 1) * L.xi s * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = _
    exact mul_right_comm _ _ _
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j * (L.xi t)⁻¹ * L.xi t' := by
    rw [hK t', hK t, mul_inv_cancel_right]
  have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.Chain.StepVac.hasInfExp_mul h (GlobalTheory.Chain.StepVac.hasInfExp_inv h0)) h0'
  rw [e]
  simpa using this

end Grid

theorem nontrivial_of_tensor {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, hu⟩ := exists_ne (0 : Pi)
  apply hu
  rw [← e.apply_symm_apply u, hz (e.symm u), map_zero]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7} {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
  [AddCommGroup Pi] [Module ℂ Pi]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7}

end GlobalTheory.SquareRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.VacX

variable {D : D7}

theorem transport (ψ ψ' : AddChar (AF D.host.F) ℂ) (θ θ' : InfFam D) (hψ : ψ' = ψ) (hθ : θ' = θ)
    {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ}
    (hcS : HEq cS cS')
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    (hcT : HEq cT cT')
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    (hΛS : HEq ΛS ΛS')
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hΛT : HEq ΛT ΛT')
    {f : WO (negSp S') T' → ℂ}
    (h : IsVacO ψ' θ' (negSp S') T' (fun τ => -cS' τ) cT' (ΛS' : Set _) (ΛT' : Set _) f) :
    ∃ f' : WO (GlobalTheory.Grid.sgn true S) T → ℂ,
      IsVacO ψ θ (GlobalTheory.Grid.sgn true S) T (fun τ => GlobalTheory.Grid.sgnM true (cS τ)) cT (ΛS : Set _) (ΛT : Set _) f' ∧ HEq f' f := by
  subst hS hT hψ hθ
  obtain rfl := eq_of_heq hcS
  obtain rfl := eq_of_heq hcT
  obtain rfl := eq_of_heq hΛS
  obtain rfl := eq_of_heq hΛT
  exact ⟨f, h, HEq.rfl⟩

end GlobalTheory.GridJoin.VacX

open GlobalTheory.GridJoin.VacX in

theorem GlobalTheory.GridJoin.exists_vacX : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f ∧ (j = 0 → HEq f (W.vac i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hag _ i j hi hj
  have hS := hag.vert (i + 1) j (by omega) hj
  have hT := hag.vert i j (by omega) hj
  have key : ∀ f, W.IsVac (.chi i j) f → ∃ f' : WO (G.V (i + 1) j).V (G.V i j).V → ℂ,
      GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f' ∧ HEq f' f := fun f hf =>
    transport R.ψ W.ψ R.θ W.θ hW.ψ hW.θ hS.sp hT.sp hS.cart hT.cart hS.lat hT.lat hf
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨f, h1, h2⟩ := key (W.vac i) (W.vac_is i hi)
    exact ⟨f, h1, fun _ => h2⟩
  · obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .chi i j) ⟨hi, hj⟩
    obtain ⟨f', h1, -⟩ := key f hf
    exact ⟨f', h1, fun h => by omega⟩
end

