import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegral
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

def IntV {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) : Prop := ∀ i, x i ∈ PIW.ClassFinD.Ohat F

def emb {n : ℕ} (y : Fin n → F) : Fin n → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F _ (y i)

theorem intV_add {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x + y) :=
  fun i => (PIW.ClassFinD.Ohat F).add_mem (hx i) (hy i)

theorem intV_sub {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x - y) :=
  fun i => (PIW.ClassFinD.Ohat F).sub_mem (hx i) (hy i)

theorem intV_smul {n : ℕ} {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PIW.ClassFinD.Ohat F)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) : IntV (a • x) :=
  fun i => (PIW.ClassFinD.Ohat F).mul_mem ha (hx i)

theorem intV_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (hA : ∀ i j, A i j ∈ PIW.ClassFinD.Ohat F) {z : Fin n → FiniteAdeleRing (𝓞 F) F} (hz : IntV z) :
    IntV (A *ᵥ z) := fun i => by
  show ∑ j, A i j * z j ∈ _
  exact (PIW.ClassFinD.Ohat F).sum_mem fun j _ => (PIW.ClassFinD.Ohat F).mul_mem (hA i j) (hz j)

theorem intV_single {n : ℕ} (j : Fin n) : IntV (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) := fun i => by
  by_cases h : i = j
  · subst h; rw [Pi.single_eq_same]; exact (PIW.ClassFinD.Ohat F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (PIW.ClassFinD.Ohat F).zero_mem

theorem int_mem (c : 𝓞 F) : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) ∈ PIW.ClassFinD.Ohat F :=
  fun v => by
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.MainNotions.BridgeLevelGenB.val_int]
    exact HeightOneSpectrum.intValuation_le_one v c

theorem exists_int_of_mem (f : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ PIW.ClassFinD.Ohat F) :
    f ∈ (algebraMap (𝓞 F) F).range :=
  HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F f fun v => by
    have hv : algebraMap F (v.adicCompletion F) f ∈ v.adicCompletionIntegers F := h v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, PI.WAU.val_algebraMap_F] at hv

theorem exists_den (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ N : ℕ, 0 < N ∧ (N : FiniteAdeleRing (𝓞 F) F) * a ∈ PIW.ClassFinD.Ohat F :=
  PI.WAU.B.exists_nat_adele a

theorem exists_den_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, (N : FiniteAdeleRing (𝓞 F) F) * A i j ∈ PIW.ClassFinD.Ohat F := by
  classical
  choose m hm h using fun q : Fin n × Fin n => exists_den (A q.1 q.2)
  refine ⟨∏ q, m q, Finset.prod_pos fun q _ => hm q, fun i j => ?_⟩
  obtain ⟨k, hk⟩ : m (i, j) ∣ ∏ q, m q := Finset.dvd_prod_of_mem m (Finset.mem_univ _)
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : FiniteAdeleRing (𝓞 F) F), mul_assoc]
  exact (PIW.ClassFinD.Ohat F).mul_mem (natCast_mem (PIW.ClassFinD.Ohat F) k) (h (i, j))

theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : F, ∃ c ∈ PIW.ClassFinD.Ohat F, a = algebraMap F _ f + (M : FiniteAdeleRing (𝓞 F) F) * c := by
  obtain ⟨N, hN, hNa⟩ := exists_den a
  obtain ⟨s, c, hc, hs⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod (N * M) (Nat.mul_pos hN hM) _ (fun v => hNa v)
  refine ⟨algebraMap (𝓞 F) F s * (N : F)⁻¹, c, fun v => hc v, ?_⟩
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hinv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, inv_mul_cancel₀ hN0, map_one]
  calc a = algebraMap F _ ((N : F)⁻¹) * ((N : FiniteAdeleRing (𝓞 F) F) * a) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
      rw [hs, map_mul, Nat.cast_mul]
      linear_combination ((M : FiniteAdeleRing (𝓞 F) F) * c) * hinv

theorem exists_approx_vec {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : Fin n → F, ∃ c : Fin n → FiniteAdeleRing (𝓞 F) F, IntV c ∧
      x = emb f + (M : FiniteAdeleRing (𝓞 F) F) • c := by
  choose f c hc h using fun i => exists_approx (x i) M hM
  exact ⟨f, c, hc, funext fun i => by simpa [emb, smul_eq_mul] using h i⟩

theorem emb_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (y : Fin n → F) :
    (A.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ emb y = emb (A *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (FiniteAdeleRing (𝓞 F) F)) A y i).symm

variable (F) in

def lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Submodule (𝓞 F) (Fin n → F) where
  carrier := {y | IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y)}
  add_mem' := by
    intro x y hx hy
    have e : emb (x + y) = emb x + (emb y : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      ext i; simp [emb]
    show IntV _
    rw [e, mulVec_add]
    exact intV_add hx hy
  zero_mem' := by
    show IntV _
    have e : emb (0 : Fin n → F) = (0 : Fin n → FiniteAdeleRing (𝓞 F) F) := by ext i; simp [emb]
    rw [e, mulVec_zero]
    exact fun i => (PIW.ClassFinD.Ohat F).zero_mem
  smul_mem' := by
    intro c y hy
    have e : emb (c • y) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) • emb y := by
      ext i; simp [emb, Algebra.smul_def]
    show IntV _
    rw [e, mulVec_smul]
    exact intV_smul (int_mem c) hy

theorem mem_lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (y : Fin n → F) :
    y ∈ lat F s ↔ IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y) := Iff.rfl

end GlobalTheory.StabLat

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

theorem lat_fg {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : (lat F s).FG := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
  have hD0 : ((D : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hD.ne'
  refine Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hD0 fun y hy => ?_
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.mem_bnd]
  intro a
  apply exists_int_of_mem
  have hI : IntV ((D : FiniteAdeleRing (𝓞 F) F) • emb y) := by
    have e : (D : FiniteAdeleRing (𝓞 F) F) • emb y =
        ((D : FiniteAdeleRing (𝓞 F) F) • ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
          ((((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ emb y) := by
      rw [Matrix.mulVec_mulVec, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [e]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDS i j) hy
  have := hI a
  simpa [emb, map_natCast] using this

theorem lat_span {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Submodule.span F (lat F s : Set (Fin n → F)) = ⊤ := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)))
  have hD0 : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  have hmem : ∀ j : Fin n, (D : F) • Pi.single j (1 : F) ∈ lat F s := by
    intro j
    rw [mem_lat]
    have e : emb ((D : F) • Pi.single j (1 : F)) =
        (D : FiniteAdeleRing (𝓞 F) F) • (Pi.single j 1 : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      funext i
      by_cases h : i = j
      · subst h; simp [emb]
      · simp [emb, Pi.single_eq_of_ne h]
    rw [e, Matrix.mulVec_smul]
    intro i
    rw [Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
    exact hDS i j
  rw [eq_top_iff, ← (Pi.basisFun F (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  have h1 : Pi.single j (1 : F) = (D : F)⁻¹ • ((D : F) • Pi.single j (1 : F)) := by
    rw [smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

theorem lat_isLattice {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Submodule.IsLattice F (lat F s) :=
  ⟨lat_fg s, lat_span s⟩

theorem matInt_conj {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) F)
    (h : ∀ y ∈ lat F s, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ lat F s) :
    PIW.ClassFinD.MatInt ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  set S : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := s.val with hS
  set Si : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := (s⁻¹).val with hSi
  set G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) with hG
  have hA : ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = Si * G * S := by
    rw [Units.val_mul, Units.val_mul]; rfl
  have hSiS : Si * S = 1 := by rw [hSi, hS, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSSi : S * Si = 1 := by rw [hSi, hS, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA]
  obtain ⟨N, hN, hNA⟩ := exists_den_mat (Si * G * S)
  obtain ⟨D, hD, hDSi⟩ := exists_den_mat Si
  suffices key : ∀ z, IntV z → IntV ((Si * G * S) *ᵥ z) by
    intro i j
    have := key (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) (intV_single j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  intro z hz
  obtain ⟨f, c, hc, hSz⟩ := exists_approx_vec (S *ᵥ z) (N * D) (Nat.mul_pos hN hD)
  set u : Fin n → FiniteAdeleRing (𝓞 F) F := (D : FiniteAdeleRing (𝓞 F) F) • (Si *ᵥ c) with hu
  have hui : IntV u := by
    rw [hu, ← Matrix.smul_mulVec]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDSi i j) hc
  have hz' : Si *ᵥ emb f = z - (N : FiniteAdeleRing (𝓞 F) F) • u := by
    have e : emb f = S *ᵥ z - ((N * D : ℕ) : FiniteAdeleRing (𝓞 F) F) • c := eq_sub_of_add_eq hSz.symm
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSiS, Matrix.one_mulVec, Matrix.mulVec_smul, hu,
      Nat.cast_mul, mul_smul]
  have hf : f ∈ lat F s := by
    rw [mem_lat]
    change IntV (Si *ᵥ emb f)
    rw [hz']
    exact intV_sub hz (intV_smul (natCast_mem _ N) hui)
  have hγf := h f hf
  rw [mem_lat, ← emb_mulVec, Matrix.mulVec_mulVec] at hγf
  have hzE : z = Si *ᵥ emb f + (N : FiniteAdeleRing (𝓞 F) F) • u := by rw [hz', sub_add_cancel]
  have e2 : (Si * G * S) *ᵥ z = (Si * G) *ᵥ emb f + ((N : FiniteAdeleRing (𝓞 F) F) • (Si * G * S)) *ᵥ u := by
    rw [hzE, Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_assoc (Si * G), hSSi, mul_one, Matrix.mulVec_smul,
      Matrix.smul_mulVec]
  rw [e2]
  exact intV_add hγf (intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNA i j) hui)

end GlobalTheory.StabLat

open GlobalTheory.StabLat in

theorem GlobalTheory.StabLat.exists_lattice_stab_conj :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsLattice F Λ ∧ ∀ γ : GL (Fin n) F,
        (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) →
          s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  refine ⟨lat F s, lat_isLattice s, fun γ hγ => ⟨matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ = s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroRationalLiftMemBasePart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RatLift

theorem exists_rat_lift_mem_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ _ p _ i hB
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hk : (R.toCx3 F).KForm false := hRw.kForm
  have he : (R.toCx3 F).EWnorm false := hRw.ewNorm
  have hn : 0 < (R.toCx3 F).nP false := hRw.h4pos.2.2 false
  have h5 : (R.toCx3 F).H5 F.cr false := hRw.lifts0.1
  have hr : (R.toCx3 F).RATth F.cr false := hRw.ratTh
  have h3W : (R.toCx3 F).H3W F.cr false := hRw.liftHyp0.h3W
  have ht : (lv (F.fc (R.toCx3 F).zs) false).Types := hRw.types0
  have hK : ∀ y, y ∈ ⨆ q, (R.toCx3 F).WpK false i q := fun y => CxData.liftsK ht hk he hn h5 hr h3W i y
  have hc0 : cpt A3.A.v0.embedding (0 : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) = 0 := by
    funext l; simp [cpt]
  have hWpK : (R.toCx3 F).WpK false i p ≠ ⊥ := by
    intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    let M : Submodule ℂ ((R.toCx3 F).W i) :=
      ⨆ q, ⨆ (_ : q ≠ p), (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)
    have hrat : ∀ y, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M := by
      intro y
      refine Submodule.iSup_induction _ (motive := fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M)
        (hK y) ?_ ?_ ?_
      · intro q z hz
        by_cases hq : q = p
        · subst hq
          rw [h0] at hz
          rw [(Submodule.mem_bot _).1 hz, hc0, map_zero]
          exact M.zero_mem
        · exact (le_iSup₂ (f := fun q (_ : q ≠ p) => (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) q hq)
            ⟨hz, ⟨_, rfl⟩⟩
      · rw [hc0, map_zero]
        exact M.zero_mem
      · intro a c ha hc
        have : cpt A3.A.v0.embedding (a + c) = cpt A3.A.v0.embedding a + cpt A3.A.v0.embedding c := by
          funext l; simp [cpt]
        rw [this, map_add]
        exact M.add_mem ha hc
    have hrange : LinearMap.range ((R.toCx3 F).w0C false i) ≤ M := by
      rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i))).span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i)) k) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        funext l
        simp only [Pi.basisFun_apply, cpt, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact hrat _
    have hperp : M ≤ (ℂ ∙ w)ᗮ := by
      refine iSup₂_le fun q hq => ?_
      intro v hv
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact (hH.prim.sumW i).1 p q (Ne.symm hq) w hw v hv
    have hww := hperp (hrange hw.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hww
    exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 hww)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpK
  obtain ⟨x, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hk he hn h5 hr i A3.A.μ0).2 y
  refine ⟨x, ?_, ?_⟩
  · have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding
        ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ∈ (R.toCx3 F).Wp i p := hy
    rw [(R.toCx3 F).key_lift F.cr false h5 hr i A3.A.μ0 x] at hy'
    exact hy'
  · rintro rfl
    exact hy0 (Matrix.mulVec_zero _)

end GlobalTheory.RatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory

theorem FlagBundle.bears_self : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  intro F _ ι _ m X Y Eb S φ f hR K _ w
  obtain ⟨A, hA⟩ := Eb.nonempty ((w ≫ f) (IsLocalRing.closedPoint K))
  obtain ⟨A', hA'⟩ := S.nonempty (w (IsLocalRing.closedPoint K))
  have hA₁ : A ∈ Eb.S (f (w (IsLocalRing.closedPoint K))) := (Scheme.Hom.comp_apply w f (IsLocalRing.closedPoint K)) ▸ hA
  have hN := hR.2.1 _ A' hA' A hA₁
  have hh : Par 0 ⊤ ((A' * (A.map φ)⁻¹).map ((ratOf Y).val w)) := by
    have hz := RatModel.range_eq_singleton (M := ratOf Y) w (IsLocalRing.closedPoint K)
    exact hN.map_of ((ratOf Y).val w) (RatModel.valHom (M := ratOf Y) w _ hz)
      (fun x => (RatModel.valHom_apply (M := ratOf Y) w _ hz x).symm)
  refine ⟨A, hA, _, hh, A', hA', ?_⟩
  rw [Mat.mul_inv hh.det_ne]
  exact Par.one
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOverStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  first | exact @GlobalTheory.FlagBundle.exists_projBundle | exact GlobalTheory.FlagBundle.exists_projBundle | (intros; apply GlobalTheory.FlagBundle.exists_projBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosedStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] (T : TopologicalSpace.Closeds X), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → j (genericPoint Y) ∉ T → ∃ D : CartierDiv Y, D.Eff ∧ (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧ ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g → ∀ (f : Y.functionField) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g) := by
  first | exact @GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | exact GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | (intros; apply GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullbackStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  first | exact @GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | exact GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | (intros; apply GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomialsStatement
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_types_intertwiner_matrix_polynomials : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  first | exact @GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | exact GlobalTheory.CompactHoweJoint.exists_joint_intertwiner | (intros; apply GlobalTheory.CompactHoweJoint.exists_joint_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TupChar

theorem chrEq_mul {D : D7} {c c' : IdC D} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => (congrArg₂ (· * ·) (h.1.2 x) (h'.1.2 x)).trans (mul_one _)⟩,
    fun P e he k x hx => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
  rfl

theorem unramEverywhere {D : D7} {c : IdC D} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P) :
    UnramEverywhere D c := fun x hx h4 h5 => by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_tupChars : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → ∃ (chr : D.what₂.Tup → ℕ → IdC D) (eta : IdC D), (∀ μ j, IsHC D (chr μ j)) ∧ (∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)) τ (-(D.hc τ).e j)) ∧ (∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j) 0) ∧ IsHeckeChar D eta ∧ (∀ τ, HasInfExp D eta τ (1 / 2)) ∧ ResEta D eta 1 ∧ UnramEverywhere D eta ∧ (∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (chr μ (j.1 + 1)) (C.mu0 j * xi μ)) ∧ Formalism.IndefR.Links.ChrEq eta C.eta := by
  intro D C xi hfin htriv
  classical
  choose n hn ho using hfin
  choose m hm using fun j => GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  choose x hx using fun μ => GlobalTheory.CharTransport.exists_chrEq D (xi μ) (Formalism.L2.Host.HChar.isUnitary_of_order (hn μ) (ho μ))
  obtain ⟨η, hη⟩ := GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D η C.eta hη C.isEta
  have hexp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (m j * x μ) τ (-(D.hc τ).e j) := fun μ j τ => by
    have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hm j)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (C.isMu0 j).inf) τ)
      (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hx μ) (hn μ) (ho μ) τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  let chr : D.what₂.Tup → ℕ → IdC D := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then m ⟨j - 1, by omega⟩ * x μ else 1
  have hchr : ∀ μ (j : Fin D.R.m), chr μ (j.1 + 1) = m j * x μ := fun μ j =>
    dif_pos (⟨Nat.le_add_left _ _, j.2⟩ : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ D.R.m)
  refine ⟨chr, η, fun μ j => ?_, fun μ j τ => hchr μ j ▸ hexp μ j τ, fun μ j h1 h2 => ?_, hη.1, fun τ => ?_,
    ⟨⟨_, hres⟩, fun η' h' a => ?_⟩, unramEverywhere hη C.isEta.unr, fun μ j => hchr μ j ▸ chrEq_mul (hm j) (hx μ), hη⟩
  · by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [show chr μ j = _ from dif_pos h]
      exact ⟨(chrEq_mul (hm _) (hx μ)).1, fun τ => ⟨_, hexp μ _ τ⟩⟩
    · rw [show chr μ j = _ from dif_neg h]
      exact isHC_one D
  · rw [show chr μ j = _ from dif_pos ⟨h1, h2⟩]
    refine ⟨⟨_, hres⟩, fun η' _ a => ?_⟩
    rw [pow_zero, MonoidHom.mul_apply, GlobalTheory.GridWeil.triv_base (hm _) (C.isMu0 _).triv a,
      GlobalTheory.GridWeil.triv_base (hx μ) (htriv μ) a, mul_one]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, C.isEta.inf⟩) τ
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h' hres, pow_one, MonoidHom.comp_apply]

end GlobalTheory.Mem.TupChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasureStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  first | exact @GlobalTheory.GaugeEx.exists_unique_stepRel | exact GlobalTheory.GaugeEx.exists_unique_stepRel | (intros; apply GlobalTheory.GaugeEx.exists_unique_stepRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinementStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → (∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z') → ∀ (K : Type) [Field K] (x : Sp K ⟶ M.Z), ∀ A ∈ S.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K, Par k ⊤ h → ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  first | exact @GlobalTheory.FlagBundle.StepLift.existsUnique_bears | exact GlobalTheory.FlagBundle.StepLift.existsUnique_bears | (intros; apply GlobalTheory.FlagBundle.StepLift.existsUnique_bears <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModelStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type) (m k : ι → ℕ) (S : Fr M m k), Good M d → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k), Y.dim = d ∧ Refines S S' φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_var_refines | exact GlobalTheory.FlagBundle.exists_var_refines | (intros; apply GlobalTheory.FlagBundle.exists_var_refines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGroStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.DefU.Inert.locU_equiv | exact GlobalTheory.DefU.Inert.locU_equiv | (intros; apply GlobalTheory.DefU.Inert.locU_equiv <;> assumption)
end

