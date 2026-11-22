import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links

namespace GlobalTheory.AdIsomObj

theorem adelicIsometries_obj (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.AdelicIsometries D :=
  GlobalTheory.AdIsom.adelicIsometries D

theorem frames_exist (D : D7) (V : HSp D) (N : ℕ) : ∃ β Λ, IsSDFrame V β Λ N :=
  (adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N

end GlobalTheory.AdIsomObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

section Alg

variable {R : Type} [CommRing R] {n r : ℕ}

theorem cols_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} (h : ∀ i : Fin r, ∃ a : Fin r → R, (U - 1) *ᵥ (fun k => E k i) = E *ᵥ a) :
    (U - 1) * E - E * (L * (U - 1) * E) = 0 := by
  choose a ha using h
  have e1 : (U - 1) * E = E * (Matrix.of a)ᵀ := by
    ext k i
    exact congr_fun (ha i) k
  rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc L, hL, Matrix.one_mul, sub_self]

theorem vec_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} {z : Fin n → R} {a : Fin r → R} (h : (U - 1) *ᵥ z = E *ᵥ a) :
    (U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) = 0 := by
  have e2 : L *ᵥ (E *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h, e2, sub_self]

theorem cols_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) :
    ((U - 1) * E - E * (L * (U - 1) * E)).map f =
      (U.map f - 1) * E.map f - E.map f * (L.map f * (U.map f - 1) * E.map f) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hm]

theorem vec_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (fun i => f ((((U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) : Fin n → R)) i)) =
      (U.map f - 1) *ᵥ (fun i => f (z i)) - E.map f *ᵥ ((L.map f * (U.map f - 1)) *ᵥ (fun i => f (z i))) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hm, ← Matrix.map_mul, mulVec_map, mulVec_map, mulVec_map]
  funext i
  simp only [Pi.sub_apply, map_sub]

theorem cols_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {T : Matrix (Fin r) (Fin r) R}
    (h : (M - 1) * E - E * T = 0) : M * E = E + E * T := by
  rw [sub_eq_zero, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at h
  exact h

theorem vec_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {z : Fin n → R} {b : Fin r → R}
    (h : (M - 1) *ᵥ z - E *ᵥ b = 0) : M *ᵥ z = z + E *ᵥ b := by
  rw [sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at h
  exact h

theorem coordSum_one (c : Fin r → R) (L : Matrix (Fin r) (Fin n) R) (E : Matrix (Fin n) (Fin r) R) (z : Fin n → R) :
    coordSum c L E z 1 = 0 := by
  simp [coordSum, superSum]

end Alg

theorem coordSum_flag {n r : ℕ} (c : Fin r → ℂ) {L : Matrix (Fin r) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hL : L * e = 1) (z : Fin n → ℂ) (u : Matrix (Fin n) (Fin n) ℂ) (a : Fin r → Fin r → ℂ)
    (ha : ∀ j : Fin r, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = e *ᵥ a j) :
    coordSum c L e z u = ∑ j, c j * a j j := by
  have key : ∀ j : Fin r, (L * (u - 1)) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = a j := by
    intro j
    rw [← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  have hT : ∀ i j : Fin r, j.1 = i.1 + 1 → (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j = a i i := by
    intro i j hij
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = fun k => e k j := by
      have : i.succ = Fin.castSucc j := Fin.ext (by simp [hij])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_castSucc]
    have := congr_fun (key i) i
    rw [hf] at this
    rw [← this, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
  have hb : ∀ i : Fin r, i.1 + 1 = r → ((L * (u - 1)) *ᵥ z) i = a i i := by
    intro i hi
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = z := by
      have : i.succ = Fin.last r := Fin.ext (by simp [hi])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_last]
    have := congr_fun (key i) i
    rwa [hf] at this
  have hrow : ∀ i : Fin r, (∑ j : Fin r, if j.1 = i.1 + 1 then c i * (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j else 0) =
      if i.1 + 1 < r then c i * a i i else 0 := by
    intro i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · rw [if_pos rfl, hT i ⟨i.1 + 1, h⟩ rfl]
      · intro j _ hj
        rw [if_neg]
        intro h'
        exact hj (Fin.ext h')
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro h'
      have := j.2
      omega
  unfold coordSum superSum
  simp only [hrow]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := i.2
  by_cases h : i.1 + 1 < r
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add, hb i (by omega)]

variable {D : D7}

theorem mat_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m k : ℕ} (Y : Matrix (Fin m) (Fin k) (AE D))
    (h1 : Y.map (finPart D) = 0) (h2 : ∀ ρ, Y.map ((θ ρ).comp (infPart D)) = 0) : Y = 0 := by
  ext i j
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (congr_fun (h2 ρ) i) j
  · exact congr_fun (congr_fun h1 i) j

theorem vec_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m : ℕ} (Y : Fin m → AE D)
    (h1 : (fun i => finPart D (Y i)) = 0) (h2 : ∀ ρ, (fun i => (θ ρ).comp (infPart D) (Y i)) = 0) : Y = 0 := by
  funext i
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (h2 ρ) i
  · exact congr_fun h1 i

theorem comp_incA (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) :
    ((θ ρ).comp (infPart D)).comp (incA D) = tauE D ρ :=
  RingHom.ext fun x => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 x ρ

end GlobalTheory.BesselCoords

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

local infixl:70 " *ₘ " => HMul.hMul

set_option maxHeartbeats 1000000 in

theorem besChar_atTau_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  intro D θ hθ ψ A B ι d τ u hu a ha
  obtain ⟨hgC, hgτ, hgρ⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hu.1
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have hfin : (Formalism.L2.Theta.mt B (atTau θ B τ u)).map (finPart D) = 1 := GlobalTheory.StripBorel.mt_map_fin hgC
  have hinf : ∀ ρ, (Formalism.L2.Theta.mt B (atTau θ B τ u)).map ((θ ρ).comp (infPart D)) =
      infMat D.sp.cm.sig B.gram (θ ρ) (atTau θ B τ u) := fun ρ => rfl
  have hmap : ∀ ρ {m k : ℕ} (X : Matrix (Fin m) (Fin k) D.host.E),
      (X.map (incA D)).map ((θ ρ).comp (infPart D)) = X.map (tauE D ρ) := by
    intro ρ m k X
    rw [Matrix.map_map, ← RingHom.coe_comp, comp_incA θ hθ ρ]
  have hvec : ∀ ρ {m : ℕ} (x : Fin m → D.host.E),
      (fun i => ((θ ρ).comp (infPart D)) (incA D (x i))) = fun i => tauE D ρ (x i) := by
    intro ρ m x
    funext i
    exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 (x i) ρ
  have hL' := map_leftInv (incA D) hL
  have hLτ := map_leftInv (tauE D τ) hL

  have hperp : ((d.e.map (tauE D τ))ᴴ * gramAt D B τ) *ᵥ (fun k => tauE D τ (d.z k)) = 0 := by
    have h0 := mulVec_map (tauE D τ) (perpMat B d.e) d.z
    rw [d.z_perpE] at h0
    have hm : (perpMat B d.e).map (tauE D τ) = (d.e.map (tauE D τ))ᴴ * gramAt D B τ := by
      rw [perpMat, Matrix.map_mul]
      refine congrArg₂ (· * ·) ?_ rfl
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
      exact GlobalTheory.Mem.Isom.tauE_sig D τ _
    rw [hm] at h0
    rw [h0]
    funext i
    exact map_zero _
  have h1 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ₘ d.e.map (incA D) = d.e.map (incA D) +
      d.e.map (incA D) *ₘ (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D)) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D) - d.e.map (incA D) *ₘ
        (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D)) = 0 := by
      refine mat_eq_zero θ hθ _ ?_ ?_
      · rw [cols_resid_map, hfin]; simp
      · intro ρ
        rw [cols_resid_map, hinf, hmap, hmap]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          exact cols_resid (map_leftInv (tauE D ρ) hL) fun i => by
            obtain ⟨a, -, h⟩ := hu.2.1 i
            exact ⟨a, h⟩
        · rw [hgρ ρ hρ]; simp
    exact cols_of_resid hK
  have h2 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ᵥ ratV d.z = ratV d.z +
      d.e.map (incA D) *ᵥ ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ᵥ ratV d.z - d.e.map (incA D) *ᵥ
        ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) = 0 := by
      refine vec_eq_zero θ hθ _ ?_ ?_
      · refine (vec_resid_map (finPart D) _ _ _ _).trans ?_
        rw [hfin]
        simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
      · intro ρ
        refine (vec_resid_map ((θ ρ).comp (infPart D)) _ _ _ _).trans ?_
        rw [hinf, hmap, hmap]
        have hz : (fun i => ((θ ρ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D ρ (d.z i) := hvec ρ d.z
        rw [hz]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          obtain ⟨b, hb⟩ := hu.2.2 _ hperp
          exact vec_resid (map_leftInv (tauE D ρ) hL) hb
        · rw [hgρ ρ hρ]
          simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
    exact vec_of_resid hK
  refine ⟨coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)
    (Formalism.L2.Theta.mt B (atTau θ B τ u)), ?_, ?_, ?_, ?_⟩
  · rw [← coordSum_map, hfin, coordSum_one]
  · intro ρ hρ
    show ((θ ρ).comp (infPart D)) _ = 0
    rw [← coordSum_map, hinf, hgρ ρ hρ, coordSum_one]
  · show ((θ τ).comp (infPart D)) _ = _
    rw [← coordSum_map, hinf, hgτ, hmap, hmap, hvec τ d.c]
    have hz : (fun i => ((θ τ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D τ (d.z i) := hvec τ d.z
    rw [hz]
    exact coordSum_flag _ hLτ _ u a ha
  · exact besChar_eq ψ d _ _ _ h1 h2

end GlobalTheory.BesselCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBplus

open GlobalTheory.Per GlobalTheory.Per.Inhab
open scoped Pointwise

variable {D : D7}

theorem integrable_of_haar {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}
    {Q : GA D A → GA D B → ℂ} (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hc : Continuous fun q : GA D A × NFlag B e => Q q.1 q.2) {μ : Measure (GA D A)} {𝓕 : Set (GA D A)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 μ) {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)}
    (hN : IsUnitN B e ν 𝓝) :
    (∀ g, IntegrableOn (fun n : NFlag B e => Q g n) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, Q g n ∂ν) 𝓕 μ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI := hμ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine FJConv.iterated_integrableOn hfin.ne (by rw [hN.2.2]; exact ENNReal.one_ne_top) hc (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hQ.norm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  rw [e1, hQ.conj k _ (mul_mem γ'.2 k'.2) γ hγ _ ((hs _ _).2 rfl), hQ.left k _ k'.2 _ γ'.2 hγ']

theorem isAutFun_star {V : HSp D} {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (star φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  exact ⟨fun γ hγ g => by simp only [Pi.star_apply, h.left γ hγ g],
    ⟨U, hU, fun k hk hkf g => by simp only [Pi.star_apply, hUφ k hk hkf g]⟩, h.cont.star⟩

section Col

open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols levPlus mem_cols)

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem coefPlus_fin {h : GA D (G.V (.top 0))} (hh : h ∈ GfC (G.V (.top 0))) : (coefPlus G θ).ρ h = 1 := by
  have e : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
    rw [show infHom (Xp G) h = 1 from hh, map_one]
  show GlobalTheory.CoefModel.rhoH _ _ (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) = 1
  rw [e, map_one, map_one]

theorem coefPlus_cont (hθ : IsInfFam θ) (x : (coefPlus G θ).W) : Continuous fun h => (coefPlus G θ).ρ h x := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.continuous_rhoH _ _ (fun h => invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) (fun τ => ?_) x
  refine (((GlobalTheory.CoefModel.realGL_laws hθ (Xp G)).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
  show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
  rw [map_inv]
  rfl

theorem rho_cancel (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (γ g : GA D (G.V (.top 0))) :
    ξ ((coefPlus G θ).ρ (γ * g)⁻¹ ((coefPlus G θ).ρ γ x)) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  have key : (coefPlus G θ).ρ (γ * g)⁻¹ * (coefPlus G θ).ρ γ = (coefPlus G θ).ρ g⁻¹ := by
    rw [← MonoidHom.map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [← Module.End.mul_apply, key]

theorem rho_right (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (k g : GA D (G.V (.top 0)))
    (hk : (coefPlus G θ).ρ k⁻¹ = 1) :
    ξ ((coefPlus G θ).ρ (g * k)⁻¹ x) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  rw [mul_inv_rev, MonoidHom.map_mul (coefPlus G θ).ρ k⁻¹ g⁻¹, Module.End.mul_apply, hk, Module.End.one_apply]

theorem col_right {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) (g : GA D (G.V (.top 0)))
    {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0)))) :
    Ψ ((finHom (G.V (.top 0))).rangeRestrict (g * k)) = Ψ ((finHom (G.V (.top 0))).rangeRestrict g) := by
  have hk2 : (finHom (G.V (.top 0))).rangeRestrict k ∈ levPlus G := by
    rw [Subgroup.mem_comap] at hk
    rw [levPlus, Subgroup.mem_comap, Lev.toAfE, Subgroup.mem_comap]
    exact hk
  have h1 := (mem_cols G θ Ψ).1 hΨ 1 ((finHom (G.V (.top 0))).rangeRestrict g) ⟨_, hk2⟩
  simp only [map_one, one_mul, OneMemClass.coe_one, Module.End.one_apply] at h1
  rw [map_mul]; exact h1

theorem pairVec_left (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {γ : GA D (G.V (.top 0))} (hγ : γ ∈ GQ (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (γ * g) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply]
  have h1 := (mem_cols G θ Ψ).1 hΨ ⟨γ, hγ⟩ ((finHom (G.V (.top 0))).rangeRestrict g) 1
  simp only [OneMemClass.coe_one, mul_one] at h1
  have e1 : (finHom (G.V (.top 0))).rangeRestrict (γ * g) =
      Bridge.ratF (G.V (.top 0)) ⟨γ, hγ⟩ * (finHom (G.V (.top 0))).rangeRestrict g := map_mul _ _ _
  rw [e1, h1]
  exact rho_cancel G θ ξ _ γ g

theorem pairVec_right (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0))))
    (hkf : k ∈ GfC (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (g * k) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply, col_right G θ hΨ g hk]
  exact rho_right G θ ξ _ k g (coefPlus_fin G θ (inv_mem hkf))

theorem pairVec_cont (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    Continuous (pairVec (coefPlus G θ) ξ Ψ) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hU := (congLev_open_compact (G.V (.top 0)) hV.sd.1 (G.pl.modul_ne_bot sc)).1
  refine continuous_iff_continuousAt.2 fun h0 => ?_
  have hn : h0 • (((G.Kplus).comap (Lev.finE (G.V (.top 0))) : Subgroup _) : Set (GA D (G.V (.top 0)))) ∈ nhds h0 :=
    (hU.leftCoset h0).mem_nhds ⟨1, one_mem _, mul_one h0⟩
  have hev : (fun h => pairVec (coefPlus G θ) ξ Ψ h) =ᶠ[nhds h0]
      fun h => ξ ((coefPlus G θ).ρ h⁻¹ (Ψ ((finHom (G.V (.top 0))).rangeRestrict h0))) := by
    filter_upwards [hn] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    rw [pairVec_apply]
    simp only [smul_eq_mul]
    rw [col_right G θ hΨ h0 hk]
  refine ContinuousAt.congr ?_ hev.symm
  exact ((LinearMap.continuous_of_finiteDimensional ξ).comp ((coefPlus_cont G θ hθ _).comp continuous_inv)).continuousAt

theorem pairVec_isAutFun (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    IsAutFun (G.V (.top 0)) (pairVec (coefPlus G θ) ξ Ψ) := by
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  exact ⟨fun γ hγ g => pairVec_left G θ ξ hΨ hγ g,
    ⟨_, (congLev_open_compact (G.V (.top 0)) hV.sd.1 (G.pl.modul_ne_bot sc)).1,
      fun k hk hkf g => pairVec_right G θ ξ hΨ hk hkf g⟩, pairVec_cont G θ hθ ξ hΨ⟩

end Col

theorem bplusConv_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  intro D T L sc G W M hM ξ Ψ hΨ F hF
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hφ := isAutFun_star (pairVec_isAutFun G W.θ W.θ_is ξ hΨ)
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  have hQ := bes_inv W.ψ_std hι G.besTop hs hφ hF
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  have H := integrable_of_haar hQ G.besTop.e_iso hι hA
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (((continuous_subtype_val.comp continuous_snd).mul
      ((emb_continuous hι hs).comp continuous_fst)).mul continuous_const))).mul
      ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star) hμ h𝓕 hM.unip
  unfold BplusConv
  rw [besInt_eq]
  exact H

end GlobalTheory.RowBplus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardHeckeCosetsEqCardSubmodulesSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hecke_cosets_eq_card_submodules_split_place : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
      Rc.card = Nat.card (GlobalTheory.HeckeCount.LatCount (T.Q.Dw ((i : ℕ) + 1)) p (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal)
        (Ideal.absNorm P.asIdeal ^ k)) := by
  first | exact @GlobalTheory.HeckeCosetCount.card_eq_latCount | exact GlobalTheory.HeckeCosetCount.card_eq_latCount | (intros; apply GlobalTheory.HeckeCosetCount.card_eq_latCount <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientPoincareSeries_isAutomorphic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, (∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsAutFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ModGrowth V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ (∀ g, Summable fun γ : GQ V => ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * g)‖) ∧ ∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪), ∀ g, poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) (g * k) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) g) ∧ (∃ T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M, ∀ a, T₀ a = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ (a : ∀ τ, M.H τ) τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (Function.update a τ (M.rep τ k (a τ))) = rTr V (atTau θ V τ k) (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c a) := by
  first | exact @GlobalTheory.PoinAut.poin_aut | exact GlobalTheory.PoinAut.poin_aut | (intros; apply GlobalTheory.PoinAut.poin_aut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientPoincareSeries_summable_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  first | exact @GlobalTheory.poincare_sum_bound | exact GlobalTheory.poincare_sum_bound | (intros; apply GlobalTheory.poincare_sum_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeConjPart.conj_part | exact GlobalTheory.HeckeConjPart.conj_part | (intros; apply GlobalTheory.HeckeConjPart.conj_part <;> assumption)
end
end

