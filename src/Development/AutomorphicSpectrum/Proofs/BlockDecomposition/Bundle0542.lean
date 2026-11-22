import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AutomorphicSpectrum.Proofs.JetProofs.ScalarOnComplement
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0068
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplement
section
open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.CompFrame

theorem exists_comp_frame : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ),
    Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 →
    ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool),
      Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧
      C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  intro n D ε C h1 h2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := GlobalTheory.CompanionTheory.HCSide.CentreNone.Jm_herm ε
  generalize hJ : Formalism.REAL.Jm ε = J at *
  have hAA : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h1, Matrix.one_mul]
  have hAB : C * Cᴴ * (J * C * Cᴴ * J) = 0 := by
    have e : C * Cᴴ * (J * C * Cᴴ * J) = C * (Cᴴ * J * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBA : J * C * Cᴴ * J * (C * Cᴴ) = 0 := by
    have e : J * C * Cᴴ * J * (C * Cᴴ) = J * C * (Cᴴ * J * C) * Cᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBB : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * Cᴴ * J := by
    have e : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * (Cᴴ * (J * J) * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, hJJ, Matrix.mul_one, h1, Matrix.mul_one]
  have hPh : (1 - C * Cᴴ - J * C * Cᴴ * J)ᴴ = 1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hJh,
      Matrix.mul_assoc]
  have hPP : (1 - C * Cᴴ - J * C * Cᴴ * J) * (1 - C * Cᴴ - J * C * Cᴴ * J) =
      1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA, hAB, hBA, hBB]
    abel
  have hPJ : J * (1 - C * Cᴴ - J * C * Cᴴ * J) = (1 - C * Cᴴ - J * C * Cᴴ * J) * J := by
    have e1 : J * (J * C * Cᴴ * J) = C * Cᴴ * J := by
      simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    have e2 : J * C * Cᴴ * J * J = J * (C * Cᴴ) := by
      rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
    abel
  subst hJ
  obtain ⟨m, ε', R, r1, r2, r3⟩ := GlobalTheory.CompanionTheory.HCSide.CentreNone.exists_frame_J hPh hPP hPJ
  refine ⟨m, R, ε', r1, r3, ?_, ?_⟩
  · have hCP : Cᴴ * (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) = 0 := by
      have e : Cᴴ * (Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) =
          (Cᴴ * Formalism.REAL.Jm ε * C) * Cᴴ * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_sub, e, h2, ← Matrix.mul_assoc, h1]
      simp
    have e : R = (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) * R := by
      rw [← r2, Matrix.mul_assoc, r1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  · rw [r2]; abel

end GlobalTheory.CompanionTheory.Dblock.CompFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwEntries

variable {E : Type} [Field E] [NumberField E]

theorem rel_le_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem rel_lt_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem mem_KGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.LFun.KGL w n → ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, h2 i j⟩,
      hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem mem_KO_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) ↔
      (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) →
      ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (rel_le_one_iff w _).1 (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    let O := ValuativeRel.valuation (w.adicCompletion E) |>.integer
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, (rel_le_one_iff w _).2 (h1 i j)⟩,
      Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, (rel_le_one_iff w _).2 (h2 i j)⟩, hi ?_, hi ?_⟩,
      Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem iwGL_KGL_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  intro E _ _ _ w n g
  refine ⟨?_, mem_KGL_iff w n g⟩
  show g ∈ GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n) ↔ _
  rw [GlobalTheory.SmGL.mem_iwahori, mem_KO_iff, and_assoc]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun i j _ => rel_lt_one_iff w _))

end GlobalTheory.CompanionTheory.IwEntries
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedVectorLift
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

noncomputable section

namespace GlobalTheory.CompanionTheory.JacquetLemma

noncomputable def vecStab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (u : V) :
    Subgroup G :=
  _root_.UpperTheory.Reformulated.B.VectorStabilizer₂.vecStab π u

def cosetStab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (q : Submodule ℂ V) (u : V) : Subgroup G where
  carrier := {x | ∀ v, π x v - u ∈ q ↔ v - u ∈ q}
  mul_mem' := by
    intro a b ha hb v
    rw [map_mul, Module.End.mul_apply, ha, hb]
  one_mem' := by intro v; simp
  inv_mem' := by
    intro a ha v
    have := ha (π a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem mem_of_pow_mem {Q : Type} [AddCommGroup Q] [Module ℂ Q] (S : Submodule ℂ Q)
    [FiniteDimensional ℂ S] (A : Module.End ℂ Q) (hA : Function.Injective A)
    (hS : ∀ x ∈ S, A x ∈ S) (j : ℕ) (w : Q) (hw : (A ^ j) w ∈ S) : w ∈ S := by
  have step : ∀ x, A x ∈ S → x ∈ S := by
    intro x hx
    let B : S →ₗ[ℂ] S := LinearMap.restrict A hS
    have hB : Function.Injective B := by
      intro p q h
      apply Subtype.ext
      apply hA
      exact congrArg Subtype.val h
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hB) ⟨A x, hx⟩
    have h2 : A y = A x := congrArg Subtype.val hy
    rw [← hA h2]
    exact y.2
  induction j with
  | zero => simpa using hw
  | succ n ih =>
    apply ih
    apply step
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hw

theorem exists_fixed_lift {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (J L A : Subgroup G) (hJo : IsOpen (J : Set G))
    (hJc : IsCompact (J : Set G)) (π : Representation ℂ G V) (hπ : IsSmooth π)
    (q : Submodule ℂ V) (u : V) (hLJ : L ≤ J) (hLu : ∀ y ∈ L, π y u = u) (hAJ : A ≤ J)
    (hAq : ∀ x ∈ A, π x u - u ∈ q) (hfact : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) :
    ∃ v ∈ fixed π J, v - u ∈ q :=
  _root_.UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift J L A hJo hJc π hπ q u hLJ hLu hAJ hAq hfact

theorem rep_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) : Function.Injective (ρ g) := by
  intro x y h
  have := congrArg (ρ g⁻¹) h
  simpa [← Module.End.mul_apply, ← map_mul] using this

end GlobalTheory.CompanionTheory.JacquetLemma

namespace GlobalTheory.CompanionTheory.JacquetLemma

theorem jacquet_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ w hw
  obtain ⟨a, hac, hstrict, hshrink⟩ := GlobalTheory.T.central_strictly_dominant_exists k N h d hd J hJo hJc hI hpos
  obtain ⟨T, hT⟩ := GlobalTheory.T.jacquet_hecke_condition_holds k N J hJo hJc V π hπ.1 (leviEmb k (stdBlocks d hd) a)
  have hC2 := GlobalTheory.T.jacquet_hecke_compat_holds k N h d hd J hJo hJc hI hpos V π hπ.1 a hstrict.1 T hT
  haveI : FiniteDimensional ℂ (fixed π J) := hπ.2 J hJo hJc
  set q := twKer π (unipRad k (stdBlocks d hd)) 1 with hq
  let p : fixed π J →ₗ[ℂ] (V ⧸ q) := q.mkQ.comp (fixed π J).subtype
  let S : Submodule ℂ (V ⧸ q) := LinearMap.range p
  haveI : FiniteDimensional ℂ S := inferInstanceAs (FiniteDimensional ℂ (LinearMap.range p))
  let A : Module.End ℂ (V ⧸ q) := jac (stdBlocks d hd) π a
  have hAinj : Function.Injective A := rep_injective _ a
  have hAS : ∀ x ∈ S, A x ∈ S := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v, ?_⟩
    have h1 := hC2 v
    show (Submodule.Quotient.mk (((((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v : fixed π J) : V) : V ⧸ q) = A (Submodule.Quotient.mk (v : V))
    rw [Submodule.coe_smul, Submodule.Quotient.mk_smul, h1, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨j, hj⟩ := hshrink {x | π x u = u} (hπ.1 u) (by simp)
  set g := leviEmb k (stdBlocks d hd) a with hg
  set u' : V := π (g ^ j) u with hu'

  have hpow : (A ^ j) (Submodule.Quotient.mk u) =
      (((deltaHalf k (Bl d) (a ^ j))⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk u' : V ⧸ q) := by
    have h1 : A ^ j = jac (stdBlocks d hd) π (a ^ j) := (map_pow (jac (stdBlocks d hd) π) a j).symm
    have h2 : leviEmb k (stdBlocks d hd) (a ^ j) = g ^ j := map_pow _ _ _
    rw [h1, jac_mk, h2]

  have hLu : ∀ y ∈ KNl k N J d hd, π y u' = u' := by
    intro y hy
    have h2 : π ((g ^ j)⁻¹ * y * g ^ j) u = u := hj y hy
    have h3 : y * g ^ j = g ^ j * ((g ^ j)⁻¹ * y * g ^ j) := by group
    rw [hu', ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply, h2]

  have hM : ∀ m ∈ KM k N J d hd, π (leviEmb k (stdBlocks d hd) m) u' - u' ∈ q := by
    intro m hm
    have h1 : jac (stdBlocks d hd) π m (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := by
      have := hw ⟨m, hm⟩
      simpa using this
    rw [jac_mk, GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hJc m hm] at h1
    simp only [inv_one, Units.val_one, one_smul] at h1
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u) : V ⧸ q) = Submodule.Quotient.mk u := h1
    have h3 : jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u)) =
        jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk u) := congrArg _ h2
    have h4 : (Submodule.Quotient.mk (π (g ^ j) (π (leviEmb k (stdBlocks d hd) m) u)) : V ⧸ q) = Submodule.Quotient.mk u' := by
      have e1 : ∀ z : V, jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (g ^ j) z) : V ⧸ q) := by
        intro z
        rw [hg, ← map_pow]
        rfl
      rw [e1, e1] at h3
      exact h3
    have hcomm : leviEmb k (stdBlocks d hd) m * g ^ j = g ^ j * leviEmb k (stdBlocks d hd) m := by
      have : m * a ^ j = a ^ j * m := ((Commute.pow_right (show Commute m a from (hac m).symm) j))
      have := congrArg (leviEmb k (stdBlocks d hd)) this
      simpa [map_mul, map_pow, hg] using this
    rw [← Submodule.Quotient.eq, hu', ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    exact h4
  have hMstab : ∀ m ∈ KM k N J d hd, leviEmb k (stdBlocks d hd) m ∈ cosetStab π q u' := by
    intro m hm v
    have h1 := hM m hm
    have hinj := rep_injective (jacU (stdBlocks d hd) π) m
    have e1 : ∀ z : V, jacU (stdBlocks d hd) π m (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) z) : V ⧸ q) := fun z => rfl
    rw [← Submodule.Quotient.eq] at h1 ⊢
    rw [← Submodule.Quotient.eq, ← e1]
    conv_lhs => rw [← h1, ← e1]
    exact hinj.eq_iff
  have hNstab : ∀ c ∈ unipRad k (stdBlocks d hd), c ∈ cosetStab π q u' := by
    intro c hc v
    have h1 : π c v - v ∈ q := by
      refine Submodule.subset_span ⟨⟨c, hc⟩, v, ?_⟩
      simp
    rw [← Submodule.Quotient.eq, ← Submodule.Quotient.eq, (Submodule.Quotient.eq q).2 h1]
  obtain ⟨v, hv, hvu⟩ := exists_fixed_lift J (KNl k N J d hd) (J ⊓ cosetStab π q u') hJo hJc π hπ.1 q u'
    inf_le_left hLu inf_le_left
    (fun x hx => by
      have := (hx.2 u').2 (by simp)
      exact this)
    (fun y hy => by
      obtain ⟨a', ha', b, hb, c, hc, hy'⟩ := hI y⁻¹ (inv_mem hy)
      obtain ⟨m, hm⟩ := hb.2
      have hmK : m ∈ KM k N J d hd := by
        show leviEmb k (stdBlocks d hd) m ∈ J
        rw [hm]; exact hb.1
      have hbS : b ∈ cosetStab π q u' := hm ▸ hMstab m hmK
      refine ⟨c⁻¹ * b⁻¹, ⟨J.mul_mem (J.inv_mem hc.1) (J.inv_mem hb.1),
        (cosetStab π q u').mul_mem ((cosetStab π q u').inv_mem (hNstab c hc.2)) ((cosetStab π q u').inv_mem hbS)⟩, ?_⟩
      have h5 : (c⁻¹ * b⁻¹)⁻¹ * y = a'⁻¹ := by
        have : y = (a' * b * c)⁻¹ := by rw [← hy']; simp
        rw [this]; group
      rw [h5]
      exact inv_mem ha')
  have hS' : (Submodule.Quotient.mk u' : V ⧸ q) ∈ S :=
    ⟨⟨v, hv⟩, (Submodule.Quotient.eq q).2 hvu⟩
  have hmem : (Submodule.Quotient.mk u : V ⧸ q) ∈ S := by
    refine mem_of_pow_mem S A hAinj hAS j _ ?_
    rw [hpow]
    exact S.smul_mem _ hS'
  obtain ⟨v', hv'⟩ := hmem
  exact ⟨v', hv'⟩

end GlobalTheory.CompanionTheory.JacquetLemma
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionSurjectiveHolds
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem jacquet_projection_surjective : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w := by
  intro G _ _ _ D V _ _ π hadm t ht U hU w hw
  have hA2 := GlobalTheory.T.jacquet_projection_hecke_holds G D V π hadm.1 t ht.1 U hU
  obtain ⟨j, v₀, hv₀⟩ := GlobalTheory.T.jacquet_vector_lift_dominant G D V π hadm.1 t ht w hw
  haveI : FiniteDimensional ℂ (fixed π D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  let L : fixed π D.J →ₗ[ℂ] Jacquet π D.N := (Submodule.mkQ _).comp (Submodule.subtype _)
  have hL : ∀ v : fixed π D.J, L v = D.proj π (v : V) := fun _ => rfl
  let I : Submodule ℂ (Jacquet π D.N) := LinearMap.range L
  haveI : FiniteDimensional ℂ I := LinearMap.finiteDimensional_range L
  let A : Module.End ℂ (Jacquet π D.N) := D.piN π t
  have hinj : Function.Injective A := by
    intro x y hxy
    have h : ∀ z, D.piN π t⁻¹ (A z) = z := by
      intro z
      change D.piN π t⁻¹ (D.piN π t z) = z
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h x, ← h y, hxy]
  have hmaps : ∀ x ∈ I, A x ∈ I := by
    rintro _ ⟨v, rfl⟩
    exact ⟨U v, by rw [hL, hL]; exact hA2 v⟩
  let A' : I →ₗ[ℂ] I := A.restrict hmaps
  have hinj' : Function.Injective A' := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective A' := LinearMap.injective_iff_surjective.1 hinj'
  have hback : ∀ x, A x ∈ I → x ∈ I := by
    intro x hx
    obtain ⟨i, hi⟩ := hsurj ⟨A x, hx⟩
    have : A (i : Jacquet π D.N) = A x := congrArg Subtype.val hi
    rw [← hinj this]
    exact i.2
  have hpow : ∀ (n : ℕ) x, D.piN π (t ^ n) x ∈ I → x ∈ I := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply ih
      apply hback
      rw [pow_succ', map_mul, Module.End.mul_apply] at hx
      exact hx
  obtain ⟨v, hv⟩ := hpow j w ⟨v₀, by rw [hL]; exact hv₀⟩
  exact ⟨v, by rw [← hL]; exact hv⟩

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamily
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviComm

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem row_mul {g : Matrix (Fin n) (Fin n) R} (hF : PFr s Jm Xm Ym) (hg : cT s g * Jm * g = Jm) {d d' : Fin r → R}
    (hX : g * Xm = Xm * diagonal d) (hY : g * Ym = Ym * diagonal d') :
    cT s Ym * Jm * g = diagonal d * (cT s Ym * Jm) := by
  have h1 : cT s (diagonal d') * diagonal d = 1 := by
    have e := pgram_unitary hg Ym Xm
    rw [hY, hX, hF.yx, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * diagonal d
        = cT s (diagonal d') * (cT s Ym * Jm * Xm) * diagonal d := by rw [hF.yx, Matrix.mul_one]
      _ = 1 := by rw [← e]; simp only [Matrix.mul_assoc]
  have h2 : diagonal d * cT s (diagonal d') = 1 := mul_eq_one_comm.1 h1
  have h3 : cT s (diagonal d') * (cT s Ym * Jm * g) = cT s Ym * Jm := by
    have e : cT s (g * Ym) * Jm * g = cT s Ym * Jm := by
      conv_rhs => rw [← hg]
      simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    rw [hY, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * (cT s Ym * Jm * g) = cT s (diagonal d') * cT s Ym * Jm * g := by
          simp only [Matrix.mul_assoc]
      _ = cT s Ym * Jm := e
  calc cT s Ym * Jm * g = diagonal d * cT s (diagonal d') * (cT s Ym * Jm * g) := by rw [h2, Matrix.one_mul]
    _ = diagonal d * (cT s Ym * Jm) := by rw [Matrix.mul_assoc, h3]

theorem comm_vecMulVec {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {C : Matrix (Fin n) (Fin m) R}
    {A : Matrix (Fin m) (Fin n) R} {d : Fin m → R} (hC : g * C = C * diagonal d) (hA : A * g = diagonal d * A)
    (i : Fin m) : g * vecMulVec (fun k => C k i) (A i) = vecMulVec (fun k => C k i) (A i) * g := by
  ext a b
  have e1 : ∑ k, g a k * C k i = C a i * d i := by
    have := congrFun (congrFun hC a) i
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have e2 : ∑ k, A i k * g k b = d i * A i b := by
    have := congrFun (congrFun hA i) b
    rwa [Matrix.mul_apply, Matrix.diagonal_mul] at this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k, g a k * (C k i * A i b) = (∑ k, g a k * C k i) * A i b := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = C a i * (d i * A i b) := by rw [e1, mul_assoc]
    _ = C a i * ∑ k, A i k * g k b := by rw [e2]
    _ = ∑ k, C a i * A i k * g k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineProj_map (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
      vecMulVec (fun k => adMat F C k i)
        (((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) i) := by
  have e : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      (cT (σ : E →+* E) D * J).map (inclR (F := F) (AF F)) := by
    unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul]
  rw [e]
  ext a b
  exact map_mul (inclR (F := F) (AF F)) (C a i) ((cT (σ : E →+* E) D * J) i b)

theorem leviMin_comm_projFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m) (hm : m ∈ leviMin σ J X Y) (k) :
    (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) =
      (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  obtain ⟨d, d', hX, hY⟩ := hm
  have hF := pfrA h hJ hW
  have hg := unitaryA_matHom m
  rcases k with i | i
  · simp only [projFam, Sum.elim_inl]
    rw [lineProj_map]
    exact comm_vecMulVec hX (row_mul hF hg hX hY) i
  · simp only [projFam, Sum.elim_inr]
    rw [lineProj_map]
    exact comm_vecMulVec hY (row_mul (pfr_swap hF) hg hY hX) i

end GlobalTheory.CompanionTheory.ParCocompact.LeviComm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolume
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ n _ d b v lv hlv mv hm c _ A hAc hAo
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := (GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hσ M J hJ (Fv F v) hR n _ _ mv (hW n M) (hH n) hm c).1
  exact ⟨hAo.measurableSet, hAc.measure_lt_top.ne⟩
end

