import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HLatStd

variable {D : D7} {V : HSp D}

def invM (h : Bridge.Gf V) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D)

def iv (x : Fin V.rank → D.host.E) : Fin V.rank → EAf D := fun i => x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)

theorem mem_set_iff (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D := by
  rw [GlobalTheory.StdFrameExist.latHat_iff hV]
  refine forall_congr' fun i => ?_
  rw [RingHom.map_mulVec]
  rfl

theorem iv_natCast_smul (N : ℕ) (x : Fin V.rank → D.host.E) : iv ((N : D.host.E) • x) = (N : EAf D) • iv x := by
  funext i
  simp only [iv, Pi.smul_apply, smul_eq_mul]
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
    (B := Formalism.L2.Herm.Af D.host.F)) N]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem iv_mem_of_int {x : Fin V.rank → D.host.E} (hx : ∀ i, IsIntegral ℤ (x i)) (i : Fin V.rank) :
    iv x i ∈ GlobalTheory.StdFrameExist.SI D := by
  obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hx i)
  show x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ _
  rw [← ho]
  exact GlobalTheory.StdFrameExist.tmul_one_mem o

theorem int_of_iv_mem {e : D.host.E} (he : (e ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) ∈ GlobalTheory.StdFrameExist.SI D) :
    IsIntegral ℤ e := by
  rw [← GlobalTheory.StdFrameExist.mem_ALint_iff] at he
  exact GlobalTheory.StabFin.isIntegral_of_mem e he

theorem mulVec_natCast_smul (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (N : ℕ) (z : Fin V.rank → EAf D) :
    M *ᵥ ((N : EAf D) • z) = ((N : EAf D) • M) *ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem invM_mul (h : Bridge.Gf V) :
    (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D) * invM h = 1 := by
  rw [invM, ← Matrix.map_mul, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem invM_hmul (h x : Bridge.Gf V) : invM (h * x) = invM x * invM h := by
  rw [invM, invM, invM, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem mem_hLat_of (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) {x : Fin V.rank → D.host.E}
    (hx : ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D) : x ∈ Bridge.hLat V h :=
  Submodule.subset_span ((mem_set_iff hV h x).2 hx)

theorem isLattice (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V h) := by
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    ((Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
  obtain ⟨N₁, hN₁, hN₁m⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (invM h)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨?_, ?_⟩
  ·
    let T : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Submodule.span (𝓞 D.host.E) (Set.range fun j : Fin V.rank => (N : D.host.E)⁻¹ • (Pi.single j (1 : D.host.E)))
    refine fg_of_le_fg (Q := T) (Submodule.fg_span (Set.finite_range _)) (Submodule.span_le.2 fun x hx => ?_)
    have hx' := (mem_set_iff hV h x).1 hx
    have hint : ∀ i, IsIntegral ℤ ((N : D.host.E) * x i) := by
      intro i
      refine int_of_iv_mem ?_
      have e1 : ((N : D.host.E) * x i) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) =
          (((N : EAf D) • (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
            *ᵥ (invM h *ᵥ iv x)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, invM_mul, Matrix.one_mulVec, ← iv_natCast_smul]
        rfl
      rw [e1]
      exact GlobalTheory.StdFrameExist.intV (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNm a b) hx' i
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hint i)
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).2 ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, smul_eq_mul, mul_one, hc]
      field_simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · simp
  ·
    refine eq_top_iff.2 ?_
    rw [← (Pi.basisFun D.host.E (Fin V.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    have hN₁E : (N₁ : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN₁.ne'
    have hint : ∀ k, IsIntegral ℤ ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) k) := by
      intro k
      rw [Pi.single_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((N₁ : EAf D) • invM h) := fun a b => by
      rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁m a b
    have hmem : (N₁ : D.host.E) • (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V h := by
      refine mem_hLat_of hV h fun i => ?_
      rw [iv_natCast_smul, mulVec_natCast_smul]
      exact GlobalTheory.StdFrameExist.intV hA (iv_mem_of_int hint) i
    have h2 : (N₁ : D.host.E) • (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈
        Submodule.span D.host.E (Bridge.hLat V h : Set (Fin V.rank → D.host.E)) := Submodule.subset_span hmem
    have h3 := Submodule.smul_mem _ (N₁ : D.host.E)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hN₁E, one_smul] at h3

theorem smul_mem_hLat_mul (hV : Seed.FrmC.StdLat V) (h x : Bridge.Gf V) (p : ℕ)
    (hp : ∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
  have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((p : EAf D) • invM x) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hp a b
  have key : ∀ y, (∀ i, (invM h *ᵥ iv y) i ∈ GlobalTheory.StdFrameExist.SI D) → (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
    intro y hy
    refine mem_hLat_of hV _ fun i => ?_
    have e : (p : 𝓞 D.host.E) • y = (p : D.host.E) • y := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e, iv_natCast_smul, mulVec_natCast_smul, invM_hmul, ← Matrix.smul_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.StdFrameExist.intV hA hy i
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (h * x)).comap ((p : 𝓞 D.host.E) • LinearMap.id) :=
    Submodule.span_le.2 fun y hy => key y ((mem_set_iff hV h y).1 hy)
  exact hle hy

theorem ratF_val (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) =
      γE.val.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) := by
  show Units.val (finHom V (γ : GA D V)) = _
  rw [finHom, MonoidHom.comp_apply, hγ]
  ext i j
  simp only [Formalism.UG.bc, incA]
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] (γE.val i j)) =
    (1 : Af D.host.F) ⊗ₜ[D.host.F] γE.val i j
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem gl_cancel {R : Type} [CommRing R] {n : ℕ} (a b : GL (Fin n) R) (v : Fin n → R) :
    Units.val (b * a)⁻¹ *ᵥ (b.val *ᵥ v) = Units.val a⁻¹ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vec_move (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    (Units.val ((Bridge.ratF V γ * h)⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      (Units.val (h⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
  have hv : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
        (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
    rw [ratF_val γ γE hγ]
    funext i
    exact RingHom.map_mulVec (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom γE.val y i
  rw [hv]
  exact gl_cancel ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) _

theorem mulVec_mem_hLat (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) : ∀ y ∈ Bridge.hLat V h, γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (Bridge.ratF V γ * h)).comap
      ((Matrix.mulVecLin γE.val).restrictScalars (𝓞 D.host.E)) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (show _ ∈ latHat D.host.F D.host.E (L0c D V) by
      rw [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, vec_move γ γE hγ h y]
      exact hy)
  exact hle hy

theorem isRatMat_inv (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Bridge.IsRatMat V γ⁻¹ γE⁻¹ := by
  unfold Bridge.IsRatMat at *
  rw [Subgroup.coe_inv, map_inv, map_inv, hγ]

theorem mem_hLat_iff (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    y ∈ Bridge.hLat V h ↔ γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  refine ⟨mulVec_mem_hLat γ γE hγ h y, fun hy => ?_⟩
  have := mulVec_mem_hLat γ⁻¹ γE⁻¹ (isRatMat_inv γ γE hγ) _ _ hy
  have e1 : Units.val γE⁻¹ *ᵥ (γE.val *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 : Bridge.ratF V γ⁻¹ * (Bridge.ratF V γ * h) = h := by rw [map_inv, inv_mul_cancel_left]
  rw [e1, e2] at this
  exact this

theorem hLat_props : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) :=
  fun _ _ hV => ⟨isLattice hV, smul_mem_hLat_mul hV, mem_hLat_iff⟩

end GlobalTheory.HLatStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleTwistRamifiedIffChosenPrimeOrConjHost
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dif_pos hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTypePlace

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom R)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hc : Nat.card (𝓞 E ⧸ PP.asIdeal) = q) (hq0 : q ≠ 0) : (q : 𝓞 E) ∈ PP.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem offPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  intro D T L μ0 hL hPg t s hs

  have hA : ∀ PP : Pl D.host.E, NG.OverPl PP s.v → ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ s.w.asIdeal →
      (p : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hov p hp
    have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← s.w_under, Ideal.mem_comap, map_natCast]; exact hp
    rw [← hov, Ideal.mem_comap, map_natCast] at h1; exact h1
  have hgne : ∀ k k' : Fin 2, k ≠ k' → D.host.g k ≠ D.host.g k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | exact D.host.g_ne | exact D.host.g_ne.symm
  obtain ⟨k, v, hkv⟩ := (hPg s.w).1 hs
  have hgk : (D.host.g k : 𝓞 D.host.E) ∈ s.w.asIdeal := by rw [hkv]; exact D.naut.plGw_over k v

  have hQ : ∀ PP ∈ L.Q t, (D.host.g k : 𝓞 D.host.E) ∈ PP.asIdeal → False := by
    intro PP hP hg
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP hP).1
    exact not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hg
      (natCast_mem_of_card PP hcard hq.ne_zero)
  have h3 : s.w ∉ L.Q t := fun h => hQ s.w h hgk
  refine ⟨?_, fun PP hP hov => hQ PP hP (hA PP hov _ hgk), h3, ?_⟩
  · intro PP hP hne hov
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s PP hov with e | hc
    · exact hne e.symm
    obtain ⟨k', v', hkv'⟩ := (hPg PP).1 hP
    have hk : k' = k := by
      by_contra hk
      have h1 : (D.host.g k' : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hkv']; exact D.naut.plGw_over k' v'
      exact not_two_primes PP.asIdeal (D.host.g_prime k') (D.host.g_prime k) (hgne k' k hk) h1
        (hA PP hov _ hgk)
    subst hk
    rw [hkv, hkv'] at hc
    exact D.naut.plGw_nconj k' v' v hc
  · by_contra hn
    rcases (hL.Q_ram t s.w).1 hn with h | ⟨PP', hP', hc⟩
    · exact h3 h
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP' hP').1
    obtain ⟨c', hc', hcq⟩ := hc _ (natCast_mem_of_card PP' hcard hq.ne_zero)
    have hq' : (q : 𝓞 D.host.E) = c' := by
      apply RingOfIntegers.ext
      rw [hcq]; simp
    exact not_two_primes s.w.asIdeal (D.host.g_prime k) hq (hqg k).symm hgk (hq' ▸ hc')

end GlobalTheory.LevelTypePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  first | exact @GlobalTheory.Mem.LiftBound.om_growth | exact GlobalTheory.Mem.LiftBound.om_growth | (intros; apply GlobalTheory.Mem.LiftBound.om_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGeneratorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  first | exact @GlobalTheory.Mem.Lift.GenZero.exists_generator | exact GlobalTheory.Mem.Lift.GenZero.exists_generator | (intros; apply GlobalTheory.Mem.Lift.GenZero.exists_generator <;> assumption)
end

