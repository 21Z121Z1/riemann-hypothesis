import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep
section
noncomputable section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.TrFinDense

theorem span_values_dense : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  intro D V S M H _ _ _ π hπ hU N hN
  classical
  set Sv : Set H := {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}
    with hSv
  set W : Submodule ℂ H := Submodule.span ℂ Sv with hW

  let Mon : Submonoid (GA D V) :=
    { carrier := {g | Sv ⊆ W.comap (π g : H →ₗ[ℂ] H)}
      mul_mem' := by
        intro a b ha hb z hz
        have hbz : π b z ∈ W := hb hz
        have : W ≤ W.comap (π a : H →ₗ[ℂ] H) := Submodule.span_le.2 ha
        show π (a * b) z ∈ W
        rw [map_mul]
        exact this hbz
      one_mem' := by
        intro z hz
        show π 1 z ∈ W
        rw [map_one]
        exact Submodule.subset_span hz }
  have hfin : ∀ g : GfC V, (g : GA D V) ∈ Mon := by
    rintro g _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU g Φ, N.apply_mem_toSubmodule g hΦ, y, rfl⟩
  have hinf : ∀ w x, embW V w x ∈ Mon := by
    intro w x
    obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
    rintro _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨Φ, hΦ, Function.update y τ (dsRep M τ x (y τ)), ?_⟩
    exact (((Φ : homDS M π ⊤).2).2 τ x y).symm
  haveI : Submodule.IsLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  have htop : Mon = ⊤ := GlobalTheory.PlaceGen.eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) Mon ∅
    (fun v x => hfin (locFin V v x)) hinf (fun k hk => hfin ⟨k, (mem_levelOff.1 hk).1⟩)
  have hinvW : ∀ g, ∀ v ∈ W, π g v ∈ W := fun g v hv =>
    (Submodule.span_le.2 (show g ∈ Mon from htop ▸ trivial)) hv
  have hsub := isSubrep_topologicalClosure (π := π) hinvW
  rcases hπ.irred.2 _ hsub with h | h
  · exfalso
    obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ ∈ N.toSubmodule, Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun Φ hΦ => (Submodule.mem_bot ℂ).2 (hc Φ hΦ)))
    have : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ≠ 0 := by
      intro e
      exact hΦ0 (Subtype.ext (Subtype.ext e))
    obtain ⟨y, hy⟩ : ∃ y, ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact this (ContinuousMultilinearMap.ext hc)
    have hmem : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ∈ W.topologicalClosure :=
      W.le_topologicalClosure (Submodule.subset_span ⟨Φ, hΦ, y, rfl⟩)
    rw [h] at hmem
    exact hy ((Submodule.mem_bot ℂ).1 hmem)
  · exact h

end GlobalTheory.TrFinDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFramesTransportLocalLatticeIsometry
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

namespace GlobalTheory.LatConjSplit

open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

noncomputable section

theorem toMatrix'_mul_symm {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

theorem toMatrix'_symm_mul {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

def compAt (τ : E →ₐ[F] Fv F v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    GL (Fin n) (Fv F v) where
  val := (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  inv := (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  val_inv := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_mul_symm, map_one]
  inv_val := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_symm_mul, map_one]

theorem compAt_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    (compAt τ a).1 = (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem compAt_inv_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    ((compAt τ a)⁻¹).1 = (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem splitVec_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a y) = (compAt τ a).1 *ᵥ splitVec τ y := by
  rw [compAt_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitVec_symm_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a.symm y) = (compAt τ a)⁻¹.1 *ᵥ splitVec τ y := by
  rw [compAt_inv_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitHom_conj (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {J J' : Matrix (Fin n) (Fin n) E}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    splitHom σ J' τ (j g) = compAt τ a * splitHom σ J τ g * (compAt τ a)⁻¹ := by
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun u => ?_))
  obtain ⟨y, rfl⟩ : ∃ y, splitVec τ y = u := ⟨splitIncl hc τ u, splitVec_splitIncl hc τ u⟩
  simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [← splitVec_matHom_mulVec, ← splitVec_symm_apply_equiv, ← splitVec_matHom_mulVec, ← splitVec_apply_equiv, ← h3,
    LinearEquiv.apply_symm_apply]

theorem conj_mem_stabLoc_iff {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v)
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v := by
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H y
    have := H (a y)
    rwa [h3, h2, h2] at this
  · intro H y'
    obtain ⟨y, rfl⟩ := a.surjective y'
    rw [h3, h2, h2]
    exact H y

theorem isSplitBasis_conj {L L' : Submodule (𝓞 E) (Fin n → E)}
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v) (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) : IsSplitBasis τ L' (compAt τ a * β) := by
  intro u
  rw [hβ u, Units.val_mul, ← Matrix.mulVec_mulVec]
  generalize β.1 *ᵥ u = z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a y, (h2 y).2 hy, splitVec_apply_equiv τ a y⟩
  · rintro ⟨y', hy', e⟩
    refine ⟨a.symm y', (h2 _).1 (by rwa [a.apply_symm_apply]), ?_⟩
    rw [splitVec_symm_apply_equiv, e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem split_conj {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J')
    (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g, s'.equiv (j g) = s.equiv g) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k → s'.red k' = s.red k := by
  obtain ⟨a, -, h2, h3⟩ := hj
  refine ⟨conj_mem_stabLoc_iff j a h2 h3, fun s => ⟨⟨s.emb, compAt s.emb a * s.basis, s.cm, hJ', hL',
    isSplitBasis_conj a h2 s.emb s.isBasis⟩, ?_⟩⟩
  have he : ∀ g, splitEquivIn s.cm hJ' s.emb (compAt s.emb a * s.basis) (j g) = s.equiv g := fun g => by
    rw [splitEquivIn_apply, splitHom_conj s.cm s.emb j a h3, SplitAt.equiv, splitEquivIn_apply]
    group
  refine ⟨he, fun k k' hk => ?_⟩
  apply Units.ext
  simp only [SplitAt.red, splitRed_val]
  congr 1
  ext i l
  rw [coe_stabLocEquiv, coe_stabLocEquiv, hk]
  exact congrArg _ (congrArg (fun x => x.1 i l) (he k))

theorem split_conj_cast {n' : ℕ} (hr : n' = n) {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (j : GLoc σ J v ≃ₜ* GLoc σ J' v)
    (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J') (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k →
        ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  subst hr
  obtain ⟨h1, h2⟩ := split_conj j hj hJ' hL'
  refine ⟨h1, fun s => ?_⟩
  obtain ⟨s', e1, e2⟩ := h2 s
  exact ⟨s', fun g a b => by rw [e1]; rfl, fun k k' hk a b => by rw [e2 k k' hk]; rfl⟩

end

end GlobalTheory.LatConjSplit

theorem GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  intro D V V' hr v j hj
  exact GlobalTheory.LatConjSplit.split_conj_cast hr j hj (GlobalTheory.Orb.isHermND_gram V') (SelfDual.isSelfDualAt_frameLat D V' v)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinZeta.SplitNorm

theorem natCast_mem_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | (apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm ..)

theorem conj_smul_ne_of_isSplit (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) : D.host.conj • w.asIdeal ≠ w.asIdeal := by
  intro hfix
  set c := GlobalTheory.Member.cF D
  have hcc : ∀ x : D.host.E, c x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hself : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    conv_rhs => rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w := fun u hu =>
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl c D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w u).1 (hu.trans hw.symm)).elim id
      fun h => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h hself
  obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := GlobalTheory.LFun.isSplit_iff.1 hv
  exact hne ((key w₁ h₁).trans (key w₂ h₂).symm)

theorem lam_qV_pow (D : D7) (lam : ℕ →* ℂ)
    (hlam : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w.under (𝓞 D.host.F) = v)
    (hv : IsSplit (E := D.host.E) v) (m : ℕ) :
    lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  apply hlam
  · exact pow_ne_zero _ fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · intro q hq hi hd
    have hmem := natCast_mem_of_dvd_absNorm w hq (hq.dvd_of_dvd_pow hd)
    refine conj_smul_ne_of_isSplit D v w hw hv (hi w.asIdeal w.isPrime w.ne_bot hmem)

end GlobalTheory.FinZeta.SplitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.OnePart

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (S : M → Prop)
    (h : ∀ x ∈ s, ∃ l : ℂ, ∀ u, S u → x u = l • u) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, ∀ u, S u → a u = l • u := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
    refine ⟨r, fun u _ => ?_⟩
    simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨l + m, fun u hu => by rw [LinearMap.add_apply, hl u hu, hm u hu, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨m * l, fun u hu => by rw [Module.End.mul_apply, hm u hu, map_smul, hl u hu, smul_smul]⟩

variable {D : D7}

theorem scalar_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ hyp V P, π k u = u) (a b : List ℤ → ℂ)
    (ha : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π P (Finsupp.single (splitLab V.rank k) 1) u = a (splitLab V.rank k) • u)
    (hb : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = b (splitLab V.rank k) • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨z, hz, hzu⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  have gen : ∀ x ∈ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
      x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∃ l : ℂ, ∀ u, S u → x u = l • u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · exact ⟨a (splitLab V.rank k), fun u hu => ha u hu k hk⟩
    · refine ⟨b (splitLab V.rank k), fun u hu => ?_⟩
      have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π u (fu u hu)
      rw [GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single] at hc
      rw [← hc]
      exact hb u hu k hk
  obtain ⟨l, hl⟩ := adjoin_scalar _ S gen z hz
  exact ⟨l, fun u hu => by rw [← hzu u (fu u hu), hl u hu]⟩

theorem postOn_hk_single {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = opOf (rRep M) P (Finsupp.single d 1) U := by
  unfold rRep
  simp only [hk, opOf, Finsupp.sum_single_index, one_smul, zero_smul]
  ext v g
  simp [postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply, Finset.sum_apply]

private theorem star_algebraMap_eq (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c := by
  have hm : (algebraMap D.host.F D.host.E c) ∈ NumberField.maximalRealSubfield D.host.E :=
    NumberField.IsTotallyReal.le_maximalRealSubfield D.host.F c.2
  exact (NumberField.IsCMField.complexConj_eq_self_iff _ _).mpr hm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem good_conj (R : RealDat D A Ks) (t : T0) (P : Pl D.host.E) (hP : Good R t P) : Good R t (Formalism.DivisionValues.conjPl P) := by
  intro PP hPP
  obtain ⟨h1, h2⟩ := hP PP hPP
  rw [GlobalTheory.GoodPrimes.isConjPl_iff] at h2 ⊢
  refine ⟨fun e => h2 ?_, fun e => h1 ?_⟩
  · rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  · have e' := congrArg Formalism.DivisionValues.conjPl e
    rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at e'
    exact e'.symm

theorem good_of_offS (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (P : Pl D.host.E)
    (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P) : Good R A.μ0 P := by
  classical
  intro PP hPP
  have hPg : PP ∈ R.Pg := by
    rcases hPP with h1 | h1
    · exact h1
    · rw [GlobalTheory.LiftLower.Q_base hL] at h1
      simp at h1
  obtain ⟨x, hx, hy⟩ := h (PP.under (𝓞 D.host.F)) (Finset.mem_image_of_mem _ hPg)
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (x : D.host.F) := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E,
          IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]; rfl)
  have hnot := hy _ hcoe
  refine ⟨fun e => hnot (by rw [← e]; exact hx'), fun hc => ?_⟩
  obtain ⟨c', hc'P, hc'eq⟩ := hc _ hx'
  exact hy c' (by rw [hc'eq, hcoe, star_algebraMap_eq]) hc'P

private theorem primeIdem_and_sphOp_of_isHeckeOpFull {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E} {d : List ℤ} {Rp : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d Rp) :
    (∃ e f, IsPrimeIdem P e f ∧ OffS D Sb P ∧ (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
      (∀ g ∈ J, SuppF V f g → χ g = 1)) ∧ SphOp V P d Rp := by
  unfold Hecke₂ at h
  obtain ⟨e, f, ϖ, α, hS, hPf, h1, h2, h3, hJ, hχ, hα, hd, hR, hc⟩ := h
  refine ⟨⟨e, f, hPf, hS, hJ, hχ⟩, ?_⟩
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun hk => ⟨(hJ k hk.2).1 hk.1, hk.2⟩, fun hk => ⟨(hJ k hk.2).2 hk.1, hk.2⟩⟩
  unfold SphOp Hecke₂
  refine ⟨e, f, ϖ, α, GlobalTheory.LevOp.offS_empty, hPf, h1, h2, h3, fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hd, hR, ?_⟩
  rw [← hset]
  exact hc

private theorem mult_map_mul_right_eq_of_chi_eq_one {θ} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J) (hχ : χ k = 1) :
    ∀ v g, U v (g * k) = U v g := by
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v g
    rw [hT.lev v k hk g, hχ, one_mul]
  | zero => intro v g; rfl
  | add T T' _ _ h1 h2 =>
    intro v g
    simp only [MultilinearMap.add_apply, Pi.add_apply, h1 v g, h2 v g]
  | smul c T _ h1 =>
    intro v g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1 v g]

theorem mem_one_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hM i σ b
  classical
  obtain ⟨Sw, hSw⟩ : ∃ Sw : MMap (R.MW i σ) → Prop, ∀ u, Sw u ↔ ∃ w : (R.HW i σ).H,
      (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d →
        postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) ∧
      u = (R.HW i σ).e w := ⟨_, fun _ => Iff.rfl⟩
  refine ⟨fun P d => if h : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u
    then h.choose else 0, ?_⟩
  intro w hw
  have hW : ∀ w' : (R.HW i σ).H, (R.HW i σ).e w' ∈ R.Wall i σ := by
    intro w'
    rw [← (hM i σ).2.1]
    exact LinearMap.mem_range_self _ w'
  simp only [GlobalTheory.LiftLower.partH, Submodule.mem_comap, partFull, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨hW w, ?_⟩
  intro P d Rp hfull
  obtain ⟨⟨e, f, hPf, hS, hJ, hχ⟩, hsph⟩ := primeIdem_and_sphOp_of_isHeckeOpFull hfull
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := good_of_offS R hL P hS
  have hfix : ∀ w' : (R.HW i σ).H, ∀ k ∈ hyp (Wc D i) P,
      rRep (R.MW i σ) k ((R.HW i σ).e w') = (R.HW i σ).e w' := by
    intro w' k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.LevOp.mem_hyp hPf).1 hk
    have hkJ := (hJ k hk2).2 hk1
    have hinv := mult_map_mul_right_eq_of_chi_eq_one (hW w') k hkJ (hχ k hkJ hk2)
    unfold rRep
    ext v g
    simp [postOn, rLin, LinearMap.compMultilinearMap_apply, hinv]
  have hSfix : ∀ u, Sw u → ∀ k ∈ hyp (Wc D i) P, rRep (R.MW i σ) k u = u := by
    intro u hu k hk
    obtain ⟨w', -, rfl⟩ := (hSw u).1 hu
    exact hfix w' k hk
  have hex : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u := by
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · refine ⟨b P d, fun u hu => ?_⟩
      obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
      rw [← postOn_hk_single]
      exact hw' P d hG (Or.inr ⟨hc, Rp, hsph⟩)
    · refine scalar_of_split (rRep (R.MW i σ)) P hc Sw hSfix (b P) (b (Formalism.DivisionValues.conjPl P)) ?_ ?_ d
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        exact hw' P _ hG (Or.inl ⟨hc, k, hk, rfl⟩)
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        refine hw' (Formalism.DivisionValues.conjPl P) _ (good_conj R A.μ0 P hG) (Or.inl ⟨?_, k, hk, rfl⟩)
        rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
        exact fun h => hc h.symm
  have hsum : heckeOn (R.MW i σ) Rp ((R.HW i σ).e w) = ∑ γ ∈ Rp, rRep (R.MW i σ) γ ((R.HW i σ).e w) := by
    unfold rRep
    ext v g
    simp [heckeOn, postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply]
  rw [hsum, ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors (Wc D i) P).1 d Rp hsph).2 _ (rRep (R.MW i σ)) _ (hfix w), dif_pos hex]
  exact hex.choose_spec _ ((hSw _).2 ⟨w, hw, rfl⟩)

end GlobalTheory.ConjScalar.OnePart

end
end

