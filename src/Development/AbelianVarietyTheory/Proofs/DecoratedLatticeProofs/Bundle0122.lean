import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceOverTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.LocMod.Inhab

theorem exists_place_over_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

theorem exists_isSplitIdem : ∀ D : D7, ∃ e : Formalism.L2.Theta.AE D, IsSplitIdem D e := by
  intro D
  obtain ⟨v, hv⟩ := exists_place_over_two D.host.F
  obtain ⟨e, he1, he2, he3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v hv
  exact ⟨e, (GlobalTheory.IdemModTwo.isSplitIdem_iff e).2 ⟨v, he1, he2, he3⟩⟩

end GlobalTheory.LocMod.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

theorem mul_mul_mul_of_gram {a b c e n : Type*} [Fintype b] [Fintype c] [Fintype e] {R : Type*} [Semiring R]
    {A : Matrix a b R} {G : Matrix b c R} {M : Matrix c e R} {C : Matrix a e R} (h : A * G * M = C)
    (N : Matrix e n R) : A * (G * (M * N)) = C * N := by
  rw [← h]; simp only [Matrix.mul_assoc]

def selFirst (D : D7) (σ : ℕ) : Matrix (Fin σ) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun i j => if j = i.castSucc then 1 else 0

def lastE (D : D7) (σ : ℕ) : Fin (σ + 1) → D.host.E := Pi.single (Fin.last σ) 1

def besselRationalBasePointMatrix (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem ell_succ_eq : ell D (σ + 1) = fun i => incA D (lastE D σ i) := by
  funext i
  by_cases h : i = Fin.last σ
  · subst h
    show (if (Fin.last σ).1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ (Fin.last σ))
    rw [if_pos (by rw [Fin.val_last]), lastE, Pi.single_eq_same, map_one]
  · have h' : ¬ (i.1 + 1 = σ + 1) := fun h' => h (Fin.ext (by rw [Fin.val_last]; omega))
    show (if i.1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ i)
    rw [if_neg h', lastE, Pi.single_eq_of_ne h, map_zero]

theorem zl_eq_rat (B : BesLev D σ) : zl B = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zl, zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_x0Rat (B : BesLev D σ) : rat (besselRationalBasePointMatrix B) = x0 B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_x0Rat (B : BesLev D σ) :
    (besselRationalBasePointMatrix B)ᴴ * B.V.gram * besselRationalBasePointMatrix B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [besselRationalBasePointMatrix, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_x0Rat (B : BesLev D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (besselRationalBasePointMatrix B) : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B) := by
  rw [zl_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_x0Rat B), gram_rat B.L rfl]

theorem linearIndependent_x0Rat (B : BesLev D σ) : LinearIndependent D.host.E (besselRationalBasePointMatrix B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : besselRationalBasePointMatrix B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * besselRationalBasePointMatrix B = selFirst D σ := by
    rw [besselRationalBasePointMatrix, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_x0Rat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rationalOrbit_point_eq_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B :=
  fun _ _ B => ⟨besselRationalBasePointMatrix B, ⟨linearIndependent_x0Rat B, gramSkew_x0Rat B⟩, rat_x0Rat B⟩

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def wr (α : Frame p S n') (β : Frame p T n) : Matrix n n' k →+ WO S T where
  toFun x := (β.b * x * α.b').map p.sec
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]

theorem wr_apply (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) (i : Fin T.rank) (j : Fin S.rank) :
    wr α β x i j = p.sec ((β.b * x * α.b') i j) := rfl

theorem rd_eq (α : Frame p S n') (β : Frame p T n) (t : WO S T) :
    rd α β t = β.b' * (Matrix.map t p.pr : Matrix (Fin T.rank) (Fin S.rank) k) * α.b := rfl

theorem isHalf_wr (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : IsHalf p.e (wr α β x) := fun i j => by
  rw [wr_apply, ← p.sec_pr, p.pr_sec]

theorem wr_rd (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) : wr α β (rd α β t) = t := by
  ext i j
  rw [wr_apply, rd_eq, Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb',
    Matrix.mul_one, Matrix.map_apply, p.sec_pr, ht i j]

set_option maxHeartbeats 800000 in

theorem open_compact_sec (p : SplitPt D k) {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) :
    IsOpen {y : Matrix (Fin T.rank) (Fin S.rank) k | y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} ∧
    IsCompact {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨N, hN, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  let A : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) k) :=
    (latO S T (LS : Set _) (LT : Set _) fun _ => True).comap p.sec.mapMatrix
  have hA : ∀ y, y ∈ A ↔ y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := fun _ => Iff.rfl
  have hO : ∀ a : k, a ∈ (𝒪[k]).toAddSubgroup ↔ finPart D (p.sec a) ∈ intAE D := p.int_iff
  have key := GlobalTheory.PlaceCoord.isOpen_isCompact_of_comm (𝒪[k]).toAddSubgroup
    (Valuation.isOpen_integer (v := valuation k)) (IsNonarchimedeanLocalField.isCompact_closedBall k 1) A hN hM
    (fun y hy => by
      have ht : IsHalf p.e (y.map p.sec : WO S T) := fun i j => by
        rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
      have h1 : (N • y).map p.sec = N • y.map p.sec := Matrix.ext fun i j => map_nsmul p.sec N (y i j)
      rw [hA, h1]
      exact hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) ht) fun i j =>
        GlobalTheory.PlaceCoord.toEAf_mem ((hO _).1 (hy i j)))
    (fun y hy i j => by
      have h1 : p.sec ((M : k) * y i j) = (M : AE D) * p.sec (y i j) := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      rw [hO, h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ ((hA y).1 hy) i j)
  exact key

theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩

theorem compact_open (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) :
    IsCompact {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} ∧
      IsOpen {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} := by
  obtain ⟨ε, hε, heε⟩ := exists_idem p
  have hh : ∀ x, wr α β x ∈ GlobalTheory.PlaceModel.half S T p.e := fun x => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (isHalf_wr α β x)
  obtain ⟨ho, hc⟩ := open_compact_sec p hS.1 hT.1
  have h1 : {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} =
      {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h.1, fun h => ⟨?_, isHalf_wr α β x⟩⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 (hh x)] at h2
  rw [h1]
  refine ⟨?_, ho.preimage (f := fun x : Matrix n n' k => β.b * x * α.b')
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)⟩
  convert hc.image (f := fun y => β.b' * y * α.b)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) using 1
  ext x
  refine ⟨fun h => ⟨β.b * x * α.b', h, ?_⟩, ?_⟩
  · beta_reduce
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, α.b'b, Matrix.mul_one]
  · rintro ⟨y, hy, rfl⟩
    change (β.b * (β.b' * y * α.b) * α.b').map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
    rwa [Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb', Matrix.mul_one]

theorem exists_SB_extFun_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ Ψ : Matrix n n' k → ℂ, Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix n n' k) ∧ extFun α β Ψ = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT
  have := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨hc, ho⟩ := compact_open α β hS hT
  refine ⟨fun x => halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (wr α β x), ?_, ?_⟩
  · unfold halfInd
    convert GlobalTheory.FinPl.Comm.ite_mem_SB hc ho
  · funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      rw [wr_rd α β ht]
    · rw [if_neg ht, halfInd, if_neg fun h => ht h.2]

end GlobalTheory.FinPl.HalfInd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_fixing_first_vectors_sum : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  first | exact @GlobalTheory.TransvMid.exists_mid | exact GlobalTheory.TransvMid.exists_mid | (intros; apply GlobalTheory.TransvMid.exists_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  first | exact @GlobalTheory.TransvLast.exists_transv_simpleSum_last | exact GlobalTheory.TransvLast.exists_transv_simpleSum_last | (intros; apply GlobalTheory.TransvLast.exists_transv_simpleSum_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryEmbeddingPreimageOfFixesAnisotropic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory

theorem mt_jB_eq_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    mt S k ⬝ o.jB = o.jB := by
  obtain ⟨hL, hq⟩ := hζ
  obtain ⟨j0, hall⟩ : ∃ j0 : Fin L.rank, ∀ j : Fin L.rank, j = j0 :=
    ⟨⟨0, by omega⟩, fun j => Fin.ext (by have := j.isLt; show j.val = 0; omega)⟩
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hq
    have : ζ = 0 := funext fun j => by rw [hall j, h0]; rfl
    simp [this]
  have hv : ratV (o.iB *ᵥ ζ) = o.jB *ᵥ ratV ζ := by
    funext i; exact RingHom.map_mulVec (incA D) o.iB ζ i
  rw [hv, Matrix.mulVec_mulVec] at hk
  have hM : (mt S k ⬝ o.jB - o.jB) *ᵥ ratV ζ = 0 := by rw [Matrix.sub_mulVec, hk, sub_self]
  rw [← sub_eq_zero]
  funext i j
  rw [hall j]
  have h1 := congrFun hM i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
  rw [Fintype.sum_eq_single j0 (fun j hj => absurd (hall j) hj)] at h1
  have hu : incA D (ζ j0) * incA D (ζ j0)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
  have e : (mt S k ⬝ o.jB - o.jB) i j0 = (mt S k ⬝ o.jB - o.jB) i j0 * ratV ζ j0 * incA D (ζ j0)⁻¹ := by
    rw [mul_assoc]; show _ = _ * (incA D (ζ j0) * _); rw [hu, mul_one]
  rw [e, h1, zero_mul]; rfl

theorem mat_eq_of_splitting {R : Type} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (jA : Matrix (Fin n) (Fin a) R) (pA : Matrix (Fin a) (Fin n) R) (jB : Matrix (Fin n) (Fin b) R)
    (pB : Matrix (Fin b) (Fin n) R) (H : Matrix (Fin a) (Fin a) R) (hX : M * jA = jA * H) (hfix : M * jB = jB)
    (hsum : jA * pA + jB * pB = 1) : M = jA * H * pA + jB * pB := by
  calc M = M * (jA * pA + jB * pB) := by rw [hsum, Matrix.mul_one]
    _ = M * jA * pA + M * jB * pB := by rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = jA * H * pA + jB * pB := by rw [hX, hfix]

theorem exists_emb_of_mt_jB_eq (D : D7) (S A B : HSp D) (o : OrthDec S A B) (k : GA D S)
    (hfix : mt S k ⬝ o.jB = o.jB) : ∃ h : GA D A, k = o.emb (h, 1) := by
  have hu : adj (mt S k) ⬝ (gA S ⬝ mt S k) = gA S := GlobalTheory.MixModel.mt_unitary S k
  have hBA : adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = 0 := by
    calc adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = adj (mt S k ⬝ o.jB) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) := by rw [hfix]
      _ = adj o.jB ⬝ (gA S ⬝ o.jA) := by
        rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
      _ = 0 := o.gram_BA
  have hpB : o.pB ⬝ (mt S k ⬝ o.jA) = 0 := by
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hX : mt S k ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) := by
    calc mt S k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) + o.jB ⬝ (o.pB ⬝ (mt S k ⬝ o.jA)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hpB, Matrix.mul_zero, add_zero]
  have e1 : adj (mt S k ⬝ o.jA) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = gA A := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
    exact o.gram_AA
  set H := o.pA ⬝ (mt S k ⬝ o.jA) with hHdef
  have e2 : adj (o.jA ⬝ H) ⬝ (gA S ⬝ (o.jA ⬝ H)) = adj H ⬝ (gA A ⬝ H) := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA H]
  rw [← hX] at e2
  have hH : adj H * (gA A * H) = gA A := e2.symm.trans e1
  refine ⟨GlobalTheory.MixModel.ofMat A H hH, GlobalTheory.MixModel.mt_injective S ?_⟩
  rw [o.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  exact mat_eq_of_splitting (mt S k) o.jA o.pA o.jB o.pB H hX hfix o.sum_eq_one

theorem exists_emb_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    ∃ h : GA D A, k = o.emb (h, 1) :=
  exists_emb_of_mt_jB_eq D S A L o k (mt_jB_eq_of_fixes_lineVec D S A L o ζ hζ k hk)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFramStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → adj c' ⬝ (gA S ⬝ c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q ⬝ d.jX = d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX ⬝ b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  first | exact @GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames | exact GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames | (intros; apply GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXUnipotentMemLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
open GlobalTheory.FinPlLoc

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.LeviKeep

variable {D : D7}

def mulAA (S : HSp D) (L : Lat S) : Lat S :=
  (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) • L

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) :
    latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨α, hα, hα', r⟩
  exact ⟨α, hα, fun w hw => hα' w fun h => hw (h ▸ hv), r⟩

end GlobalTheory.FinPl.LeviKeep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZeroAt

variable {D : D7}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {P : Pl D → Prop} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) :
    ∀ i, (M *ᵥ y) i ∈ idAt D P := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittProjectionZero_mem_latticeCompletion_of_splits {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : d.p0 *ᵥ y ∈ latV S₀ L₀ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P S₀ L₀ _ hL₀).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hm v hv _).1 (GlobalTheory.FinPlLoc.smul_latV v he hy)).2.2

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {P : Pl D → Prop}
    (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, P v → MonoAt d L L₀ v) {u : Fin T₀.rank → AE D}
    (hu : u ∈ latV T₀ L₀ P) : d.j0 *ᵥ u ∈ latV T L P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T L _ hL).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hu), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace d (hm v hv) (GlobalTheory.FinPlLoc.smul_latV v he hu)

end GlobalTheory.FinPl.ExtZeroAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_subgroups_closed_normal_cocompact' : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), IsClosed (flagN d : Set (GA D V)) ∧ ∀ M : Subgroup (GA D V), (M = centre d ∨ M = radX d ∨ ∃ j, M = Nfix d j) → M ≤ flagN d ∧ IsClosed (M : Set (GA D V)) ∧ (M.subgroupOf (flagN d)).Normal ∧ ∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ (GQ V).subgroupOf M, ∃ k ∈ K, m = γ * k := by
  first | exact @GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | exact GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | (intros; apply GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIccStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧ (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | exact GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | (intros; apply GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_invariant_function_integrable : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K → (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  first | exact @GlobalTheory.Unf.jac_absConv | exact GlobalTheory.Unf.jac_absConv | (intros; apply GlobalTheory.Unf.jac_absConv <;> assumption)
end

