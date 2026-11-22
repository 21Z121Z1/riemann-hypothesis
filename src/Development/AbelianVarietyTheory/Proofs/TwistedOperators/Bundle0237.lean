import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsLieIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBound
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.LieWords

theorem dR_eq_dAct {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mat m → (H →L[ℂ] H)) : dR π = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π := by
  funext X w
  unfold dR GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit
  congr 1

theorem one_le_of_bound {m : ℕ} (hm : 3 ≤ m) {lam : Fin m → ℝ} (hc : IsHCParam lam) {B : ℝ}
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ B := by
  have hint : ∀ a c : Fin m, a < c → 1 ≤ lam a - lam c := by
    intro a c hac
    obtain ⟨ka, hka⟩ := hc.2 a
    obtain ⟨kc, hkc⟩ := hc.2 c
    have e : lam a - lam c = ((ka - kc : ℤ) : ℝ) := by push_cast; linarith
    have hpos : (0 : ℝ) < ((ka - kc : ℤ) : ℝ) := by rw [← e]; linarith [hc.1 hac]
    have h1 : (0 : ℤ) < ka - kc := by exact_mod_cast hpos
    have h2 : (1 : ℝ) ≤ ((ka - kc : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have h01 := hint ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h12 := hint ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have a0 := abs_le.mp (hB ⟨0, by omega⟩)
  have a2 := abs_le.mp (hB ⟨2, by omega⟩)
  linarith [a0.1, a0.2, a2.1, a2.2]

theorem stepConst_le {m : ℕ} (hm : 3 ≤ m) {B : ℝ} (hB : 1 ≤ B) (P : ℕ) (hP : P ≤ m + 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) P ≤ (8 * (m : ℝ) * B) ^ 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
  rw [Real.sq_sqrt hB0]
  have h12 : (m : ℝ) ^ (1 / 2 : ℝ) ≤ m := by
    calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m := Real.rpow_one _
  have h32 : (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have hPr : (P : ℝ) ≤ m + 1 := by exact_mod_cast hP
  have a1 : (m : ℝ) ^ (1 / 2 : ℝ) * B ≤ m * B := mul_le_mul_of_nonneg_right h12 hB0
  have hmB : 1 ≤ (m : ℝ) * B := by nlinarith
  have a2 : (m : ℝ) * B ≤ (m * B) ^ 2 := by nlinarith
  have a3 : (m : ℝ) ^ 2 ≤ (m * B) ^ 2 := by
    have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
    rw [mul_pow]
    calc (m : ℝ) ^ 2 = (m : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
  have a4 : 3 * (P : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have e : (8 * (m : ℝ) * B) ^ 2 = 64 * (m * B) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg ((m : ℝ) * B)]

theorem rk_le {m : ℕ} (hm : 3 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hrk : GlobalTheory.Count.rkR ε ≤ m := by
    unfold GlobalTheory.Count.rkR
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrk) (by norm_num)
  have h32 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have h0 : 0 ≤ ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have h2 : 120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (m : ℝ) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h32) (by positivity)
  nlinarith

end GlobalTheory.SepReal.LieWords

open GlobalTheory.SepReal.LieWords in

theorem GlobalTheory.SepReal.lieBound : LieBound := by
  intro m ε lam B hm hc hgap hB H _ _ π hDS v₀ hv₀
  haveI : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) π := hDS.2.2.1
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hgap2 : ∀ a b : Fin m, ε a ≠ ε b → 2 * (m : ℝ) < |lam a - lam b| := by
    intro a b hab
    have h := hgap a b hab
    nlinarith [sq_nonneg (m : ℝ)]
  have hK := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub m ε lam H π hc hDS hgap2
  have hZ := GlobalTheory.DSId.LowCharGap.lowChar m ε lam H π hc hDS _ hgap (rk_le hm ε)
  have hB1 : 1 ≤ B := one_le_of_bound hm hc hB
  have hb : ∀ a, |lam a| ≤ (Real.sqrt B) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; exact hB
  have hSB := GlobalTheory.StepBoundOneRep.stepBound_of_eigen m ε H π lam (Real.sqrt B) hU hK hZ hb
  refine ⟨?_, ?_⟩
  · have hs := GlobalTheory.StepBoundOneRep.smooth_of_mem_lowKSub ε lam π hU hK v₀ hv₀.2
    have hJ : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (Jm_mul_self ε))
    exact (GlobalTheory.SmChart.smV_iff_smoothOnH hJ hU.1 v₀).2 hs
  · rw [dR_eq_dAct]
    intro l
    induction l with
    | nil => intro _ _; simp [hv₀.1]
    | cons X l ih =>
      intro hl hlen
      have hX : inG ε X := hl X List.mem_cons_self
      have hl' : ∀ Y ∈ l, Y ∈ lieOf (Jm ε) := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hlen' : l.length ≤ m + 2 := by simp at hlen; omega
      have hmem : l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam π l.length :=
        Submodule.subset_span ⟨l, v₀, le_rfl, hl', hv₀.2, rfl⟩
      have h1 := (hSB l.length).2.2.2 X hX _ hmem
      have hcst := stepConst_le hm hB1 l.length (by simp at hlen; omega)
      have hrest := ih hl' hlen'
      have hsq : Real.sqrt (hs X) = hsn X := rfl
      have hh : 0 ≤ hsn X := Real.sqrt_nonneg _
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      calc ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π X (l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀)‖
          ≤ Real.sqrt (hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) l.length *
              ‖l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀‖ := h1
        _ ≤ ((8 * (m : ℝ) * B) ^ 2 * hsn X) * (l.map fun X => (8 * (m : ℝ) * B) ^ 2 * hsn X).prod := by
          rw [hsq]
          refine mul_le_mul ?_ hrest (norm_nonneg _) (by positivity)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hcst hh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.InfMem

theorem conjI_eq_comap (D : D7) (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj (D : D7) : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMaximal (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  haveI := PP.isMaximal
  exact Ideal.comap_isMaximal_of_surjective _ (bar_surj D)

theorem conjI_inj (D : D7) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : conjI PP.asIdeal = conjI PP'.asIdeal) : PP = PP' := by
  apply HeightOneSpectrum.ext
  ext a
  have := congrArg (fun I => GlobalTheory.SW.Lev.bar a ∈ I) h
  simp only [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this
  exact Iff.of_eq this

theorem mem_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E)
    (hx : ∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) : x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  unfold GlobalTheory.LiftLevel.liftI
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Submodule.mem_iInf]
    exact hx
  · intro PP _ PP' _ hne
    have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun h => hne (conjI_inj D h)
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (conjI_isMaximal D PP) (conjI_isMaximal D PP') hne'

theorem main : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := fun D Pg Q x hx => mem_liftI D Pg Q x hx

end GlobalTheory.LiftLevel.InfMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.InertHomIdx

variable {D : D7}

def compW (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.compAt D.host.F w).comp (finPart D)

def matW (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.FinWeilO.XF S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) where
  toFun x := (x : WO S T).map (compW D w)
  map_zero' := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_zero]
  map_add' x y := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_add]

theorem matW_apply (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : GlobalTheory.FinWeilO.XF S T) :
    matW S T w x = (x : WO S T).map (compW D w) := rfl

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) L) where
  carrier := {X | ∀ i j, X i j ∈ Formalism.UG.intL L}
  add_mem' hX hY i j := add_mem (hX i j) (hY i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hX i j := neg_mem (hX i j)

theorem mem_intMat {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) L} : X ∈ intMat L m n ↔ ∀ i j, X i j ∈ Formalism.UG.intL L := Iff.rfl

def lmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := g * X
  map_zero' := Matrix.mul_zero g
  map_add' := Matrix.mul_add g

theorem lmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) (X : Matrix (Fin m) (Fin n) L) :
    lmul g X = g * X := rfl

end GlobalTheory.InertHomIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroupStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → ℓ (ω (t, 1) s) = (-1) ^ n' * (q : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') := by
  first | exact @GlobalTheory.SphTheta.TorusFirst.value_torus_first | exact GlobalTheory.SphTheta.TorusFirst.value_torus_first | (intros; apply GlobalTheory.SphTheta.TorusFirst.value_torus_first <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCovers
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.NoLiftTransfer

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply]

theorem conj_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ

  have h2 : Jm p q * Zᴴ * Jm p q + Z = 0 := by
    have h' := congrArg (fun X => Jm p q * X) h
    simpa [mul_add, ← mul_assoc, jm_mul_jm] using h'
  have h3 : (Jm p q * Zᴴ * Jm p q).trace + Z.trace = 0 := by rw [← Matrix.trace_add, h2, Matrix.trace_zero]
  rw [Matrix.trace_mul_comm, ← mul_assoc, jm_mul_jm, one_mul, Matrix.trace_conjTranspose] at h3
  rw [starRingEnd_apply]
  exact eq_neg_of_add_eq_zero_left h3

def invConj {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) : B →ₛₗ[starRingEnd ℂ] A where
  toFun := (Equiv.ofBijective u hb).symm
  map_add' x y := by
    apply hb.1
    rw [hadd]
    simp only [Equiv.ofBijective_apply_symm_apply]
  map_smul' z x := by
    apply hb.1
    rw [hsmul]
    simp only [Equiv.ofBijective_apply_symm_apply, Complex.conj_conj]

theorem invConj_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) (x : A) : invConj u hb hadd hsmul (u x) = x :=
  hb.1 ((Equiv.ofBijective u hb).apply_symm_apply (u x))

theorem noLift_of_pairNo : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  intro D V S M τ ι σ Z A pt κ p q T₁ R₁ a₁ l₁ c₁ b₁ e₁ u₁ hK hS hP

  have hsm : ∀ (z : ℂ) x, u₁ (z • x) = conj z • u₁ x := fun z x => by simpa [cjc] using hK.smul z x
  let w := invConj u₁ hK.bij hK.add hsm
  have hw_right : ∀ y, u₁ (w y) = y := fun y => (Equiv.ofBijective u₁ hK.bij).apply_symm_apply y
  have hw_left : ∀ v, w (u₁ v) = v := fun v => invConj_apply u₁ hK.bij hK.add hsm v
  intro U _ _ Q hQ

  let B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P => (Q (κ.symm P)).comp w
      map_add' := fun P P' => by ext x; simp
      map_smul' := fun z P => by ext x; simp }
  have hB : ∀ P x, B P x = Q (κ.symm P) (w x) := fun _ _ => rfl
  have hinv : PInv a₁ R₁ B := by
    intro Y hY P x
    set t : ℂ := (c₁ : ℂ) * Y.trace with ht_def

    have ht : conj t = -t := by rw [ht_def, map_mul, conj_trace hY, map_ratCast, mul_neg]
    have hX : phiFr (M.fr τ) b₁ e₁ Y ∈ lieAt V τ := by rw [← hK.lie]; exact ⟨Y, hY, rfl⟩
    have hpol : PolDer A pt (phiFr (M.fr τ) b₁ e₁ Y) (κ.symm P) (κ.symm (a₁ Y P + t • P)) :=
      (hS.der Y hY _ _).2 (by simp only [LinearEquiv.apply_symm_apply, ht_def])
    have hvec : VecDer M τ (phiFr (M.fr τ) b₁ e₁ Y) (w x) (w (R₁.HK.act Y x + t • x)) :=
      (hK.der Y hY _ _).2 (by simp only [hw_right, ht_def])
    have h0 := hQ _ hX _ _ _ _ hpol hvec
    have e1 : Q (κ.symm (a₁ Y P + t • P)) (w x) = Q (κ.symm (a₁ Y P)) (w x) + t • Q (κ.symm P) (w x) := by
      rw [map_add, map_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    have e2 : Q (κ.symm P) (w (R₁.HK.act Y x + t • x)) =
        Q (κ.symm P) (w (R₁.HK.act Y x)) - t • Q (κ.symm P) (w x) := by
      rw [map_add, map_add, map_smulₛₗ, ht, map_smul, neg_smul, sub_eq_add_neg]
    rw [e1, e2] at h0
    rw [hB, hB, ← h0]
    abel
  have hB0 : B = 0 := hP U B hinv
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  have h1 := congrArg (fun F : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U => F (κ P) (u₁ v)) hB0
  simpa [hB, hw_left] using h1

end GlobalTheory.ArchRec.NoLiftTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.LowerTower

open GlobalTheory.SmallerSource GlobalTheory.FockAlg

theorem lamA_mem (al be ga de : List ℚ) (a : Ix (al.length + be.length) (ga.length + de.length)) :
    lamA al be ga de a ∈ al ++ be ++ ga ++ de := by
  rw [List.append_assoc (al ++ be)]
  cases a with
  | inl i => exact List.mem_append_left _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) i)
  | inr j => exact List.mem_append_right _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) j)

theorem tensNo_first (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hpq : 1 ≤ p + q) (lam : Ix p q → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair r s) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair r s) (blattner lam) a ≤ 0))
    (hno : ∀ μ', ¬ JointShape p q r s (blattner lam) μ') :
    TensNo (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) := by
  intro MM f hf
  by_contra hne
  obtain ⟨hadm, hirr⟩ := discrete_series_gk_admissible_irreducible X h5 hpq lam
  obtain ⟨hone, -, hcone⟩ := hD p q lam hlam
  have hex : ∃ v, IsHW (X.ds p q lam).HK.act (blattner lam) v := by
    have hnb : hwSub (X.ds p q lam).HK.act (blattner lam) ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hone
      exact zero_ne_one hone
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    exact ⟨v, hv0, hv⟩
  have hflow := GlobalTheory.T.degW_blattner_le_of_blattnerCone p q (X.ds p q lam).HK lam (cPair r s) θ hcone hsign
  obtain ⟨⟨μ, P, hPJ, hP1, hP2, -⟩, -⟩ :=
    GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub p q r s (X.ds p q lam).HK MM f hirr hadm hf hne (blattner lam) hex hflow
  have hbot := ((GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 (blattner lam) μ).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 (blattner lam) ⊓ hwSub (X.fock p q r s).act2 μ ⊓
      Submodule.span ℂ (X.fock p q r s).J :=
    ⟨⟨hP1.2, hP2.2⟩, Submodule.subset_span hPJ⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hP1.1 hmem

theorem tensNo_second (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam)) :
    TensNo (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam) := by
  intro MM f hf
  set c := TensorProduct.comm ℂ (X.ds r s lam).HK.V MM.V with hc
  have hcm : ∀ (A : Module.End ℂ (X.ds r s lam).HK.V) (B : Module.End ℂ MM.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hg : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK ((c : _ →ₗ[ℂ] _) ∘ₗ f) := by
    refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct1 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
    · have := LinearMap.congr_fun (hf.1 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct2 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
  have h0 := intw_eq_zero X (GlobalTheory.JointHarm.fock_polynomials X) hD h5 hrs lam hlam θ hsign hno MM _ hg
  refine LinearMap.ext fun P => ?_
  have : c (f P) = 0 := LinearMap.congr_fun h0 P
  exact c.map_eq_zero_iff.1 this

theorem no_map_lower : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  intro X hD h5 t al be ga de hA i hi
  have ht : 1 ≤ t := hA.1
  have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  obtain ⟨-, hpar, hpar', hsign, hsign'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨hno, -, hno'⟩ := GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi
  refine ⟨fun hr hs => ?_, fun hbig hp hq => ?_⟩
  · refine tensNo_first X hD h5 (by omega) _ hpar 0 ?_ (hno hr hs)
    rw [cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith
  · refine tensNo_second X hD h5 (by omega) _ hpar' ((t : ℚ) / 2) ?_ (hno' (.inl ?_) hp hq).1
    · rw [cPair_sub hp hq]
      exact hsign'
    · rintro ⟨a, ha⟩
      have := hbig _ (lamA_mem al be ga de a)
      rw [ha, abs_of_nonneg (by positivity)] at this
      linarith

end GlobalTheory.LowerTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElementsStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k], ∀ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ) (x' : plusUnits P k) (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), ((QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x' → ∃ g : HA k σ J, ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ (IsConj (gam h) (gam h') → (QuotientGroup.mk x : Cls P k) = QuotientGroup.mk x') ∧ (∀ g : HA k σ J, gam h' = g * gam h * g⁻¹ → ∀ t, torEmb h' t = g * torEmb h t * g⁻¹) ∧ ∀ g : HA k σ J, HasCls P k J (g * gam h * g⁻¹) (QuotientGroup.mk x) := by
  first | exact @GlobalTheory.TrEll.cls_conj_torus | exact GlobalTheory.TrEll.cls_conj_torus | (intros; apply GlobalTheory.TrEll.cls_conj_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPrimesSquarefreeConjugateIdealProdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_primes_squarefree_conjugateIdeal_prod : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), Squarefree (∏ PP ∈ P, PP.asIdeal) ∧ (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (∏ PP ∈ P, PP.asIdeal) ≤ PP'.asIdeal ↔ PP' ∈ P) ∧ conjI (∏ PP ∈ P, PP.asIdeal) = ∏ PP ∈ P, conjI PP.asIdeal := by
  first | exact @GlobalTheory.primeProd_squarefree_le_conj | exact GlobalTheory.primeProd_squarefree_le_conj | (intros; apply GlobalTheory.primeProd_squarefree_le_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCMStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  first | exact @GlobalTheory.TrEll.Hasse.rational_eq_local | exact GlobalTheory.TrEll.Hasse.rational_eq_local | (intros; apply GlobalTheory.TrEll.Hasse.rational_eq_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_total_degree_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  first | exact @GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le | exact GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le | (intros; apply GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le <;> assumption)
end

