import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFrobeniusSemisimplification
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.WeilDeligne

theorem isNilpotent_map_left {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X : Module.End K U} (Y : Module.End K W) (hX : IsNilpotent X) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem isNilpotent_map_right {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (X : Module.End K U) {Y : Module.End K W} (hY : IsNilpotent Y) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem commute_map {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X X' : Module.End K U} {Y Y' : Module.End K W}
    (hX : Commute X X') (hY : Commute Y Y') :
    Commute (TensorProduct.map X Y) (TensorProduct.map X' Y') := by
  show TensorProduct.map X Y * TensorProduct.map X' Y' = TensorProduct.map X' Y' * TensorProduct.map X Y
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hX.eq, hY.eq]

theorem IsFrobSS.tensor : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → Module.End ℂ V} {N : Module.End ℂ V} {a : WDRep h V} {ρ' : ↥(Weil h) → Module.End ℂ V'} {N' : Module.End ℂ V'} {b : WDRep h V'}, IsFrobSS ρ N a → IsFrobSS ρ' N' b → IsFrobSS (fun g => TensorProduct.map (ρ g) (ρ' g)) (N.rTensor V' + N'.lTensor V) (a.tensor b) := by
  intro E Ω _ _ _ _ _ A w h V V' _ _ _ _ _ _ ρ N a ρ' N' b ha hb
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ]
    exact commute_map (ha.2 g).1 (hb.2 g).1
  · rw [WDRep.tensor_ρ]
    have e : TensorProduct.map (ρ g) (ρ' g) - TensorProduct.map (a.ρ g) (b.ρ g) =
        TensorProduct.map (ρ g - a.ρ g) (ρ' g) + TensorProduct.map (a.ρ g) (ρ' g - b.ρ g) :=
      TensorProduct.ext' fun x y => by
        simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    rw [e]
    refine Commute.isNilpotent_add ?_ (isNilpotent_map_left _ (ha.2 g).2)
      (isNilpotent_map_right _ (hb.2 g).2)
    exact commute_map ((ha.2 g).1.symm.sub_left (Commute.refl _))
      ((Commute.refl _).sub_right (hb.2 g).1.symm)

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.ThetaRiesz

theorem thetaPair_of_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  intro k _ _ _ _ r n V W _ _ _ _ μ σ π hadm hunit hμ b hb hb_inv
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hunit
  obtain ⟨hone, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ

  have huniq : ∀ u u' : V, (∀ w, Bf u w = Bf u' w) → u = u' := by
    intro u u' h
    by_contra hne
    have hne' : u - u' ≠ 0 := sub_ne_zero.2 hne
    have hfun : Bf (u - u') = 0 := by rw [map_sub, LinearMap.ext h, sub_self]
    have h0 : Bf (u - u') (u - u') = 0 := by rw [hfun, LinearMap.zero_apply]
    have := hpos _ hne'
    rw [h0] at this
    simp at this

  let S : SB (Matrix (Fin n) (Fin r) k) → Subgroup (GL (Fin r) k) := fun Φ =>
    { carrier := {g | om μ g 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ}
      one_mem' := hone _
      mul_mem' := by
        intro x y hx hy
        show om μ (x * y) 1 _ = _
        have := hmul x y 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [mul_one] at this
        rw [this]
        have hy' : om μ y 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hy
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        rw [hy', hx']
      inv_mem' := by
        intro x hx
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        show om μ x⁻¹ 1 _ = _
        have := hmul x⁻¹ x 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [inv_mul_cancel, mul_one, hx', hone] at this
        exact this.symm }
  have hSo : ∀ Φ, IsOpen ((S Φ : Subgroup _) : Set (GL (Fin r) k)) := by
    intro Φ
    have h1 := hop _ Φ.2
    have hc : Continuous (fun g : GL (Fin r) k => (g, (1 : GL (Fin n) k))) :=
      continuous_id.prodMk continuous_const
    exact h1.preimage hc
  have hL : ∀ Φ a, ∀ s ∈ S Φ, ∀ w, b Φ a (σ s w) = b Φ a w := by
    intro Φ a s hs w
    have hs' : om μ s 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hs
    have := hb_inv s 1 Φ Φ hs'.symm a w
    simpa using this
  have hex : ∀ Φ a, ∃ u : V, ∀ w, b Φ a w = Bf u w := fun Φ a =>
    exists_vector_of_smooth_antilinear k r V σ Bf hadm hsym hpos hinv (b Φ a) (S Φ) (hSo Φ) (hL Φ a)
  choose f hf using hex
  have hadd1 : ∀ Φ Ψ a, f (Φ + Ψ) a = f Φ a + f Ψ a := fun Φ Ψ a =>
    huniq _ _ fun w => by rw [← hf, map_add, LinearMap.add_apply, LinearMap.add_apply, hf, hf, map_add, LinearMap.add_apply]
  have hsmul1 : ∀ (z : ℂ) Φ a, f (z • Φ) a = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  have hadd2 : ∀ Φ a a', f Φ (a + a') = f Φ a + f Φ a' := fun Φ a a' =>
    huniq _ _ fun w => by rw [← hf, map_add, LinearMap.add_apply, hf, hf, map_add, LinearMap.add_apply]
  have hsmul2 : ∀ (z : ℂ) Φ a, f Φ (z • a) = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  let B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V :=
    LinearMap.mk₂ ℂ f hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ Φ a, B Φ a = f Φ a := fun _ _ => rfl
  refine ⟨B, ?_, ?_⟩
  · intro h0
    apply hb
    ext Φ a w
    rw [hf, ← hB, h0]
    simp
  · intro g h Φ Φ' hΦ F
    rw [hB, hB]
    apply huniq
    intro c
    have hc : σ g (σ g⁻¹ c) = c := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← hf, ← hc, hb_inv g h Φ Φ' hΦ F, hf, ← hinv g (f Φ F) (σ g⁻¹ c)]

end GlobalTheory.ThetaRiesz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ConjMatch

variable {D : D7}

theorem conj_eq_cP (P : Pl D.host.E) : Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)

theorem conj_conj (P : Pl D.host.E) : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := by
  rw [conj_eq_cP, conj_eq_cP]
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem isPrimeIdem_conj {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    IsPrimeIdem (Formalism.DivisionValues.conjPl P) (cA D e) f := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) := by
      rw [conj_eq_cP]
      obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
      exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
        by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩
    exact Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩
  · have hc := GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε
    have ht' := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [← conj_eq_cP] at ht'
    rw [hc] at ht' ⊢
    exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩

theorem isVacAt_conj (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ)
    (h : IsVacAt ψ S T P f) : IsVacAt ψ S T (Formalism.DivisionValues.conjPl P) f := by
  refine ⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩
  · have := isPrimeIdem_conj hP
    rwa [conj_conj] at this
  · rw [Formalism.L2.Theta.cA_cA]
    exact hh.symm

theorem one_mem_hyp (V : HSp D) (P : Pl D.host.E) : (1 : GA D V) ∈ hyp V P := by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h,
    (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem match_conj : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  intro D ψ S T χS χT om P _
  have hv : ∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f := fun f =>
    ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩
  refine ⟨hv, fun hF => ?_⟩
  have hS := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel S P
  have hT := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel T P
  refine ⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f := fun f hf c =>
    hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f := fun f hf c =>
    hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk
  constructor
  · intro h f hf
    rw [← eS f hf, ← eT f hf]
    exact h f ((hv f).2 hf)
  · intro h f hf
    have hf' := (hv f).1 hf
    rw [eS f hf', eT f hf']
    exact h f hf'

end GlobalTheory.Hk3.ConjMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.TrDualExpand

variable {K : Type} [Field K]

theorem iter_mul (σ : K →+* K) (n : ℕ) (a b : K) : σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem sum_zmod_val {d : ℕ} [NeZero d] (F : ℕ → K) :
    ∑ s : ZMod d, F s.val = ∑ n ∈ Finset.range d, F n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_bijective (fun s : ZMod d => (⟨s.val, ZMod.val_lt s⟩ : Fin d))
    ⟨fun a b h => ZMod.val_injective d (by simpa using congrArg Fin.val h),
     fun i => ⟨(i.val : ZMod d), by ext; simp [ZMod.val_natCast_of_lt i.2]⟩⟩ _ _ (fun _ => rfl)

theorem sum_range_even (m : ℕ) (G : ℕ → K) :
    ∑ n ∈ Finset.range (2 * m), (if n % 2 = 0 then G n else 0) = ∑ i ∈ Finset.range m, G (2 * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, if_pos (by omega), if_neg (by omega), add_zero]

theorem even_case {m d : ℕ} [NeZero d] (hd : 2 * m = d) (σ : K →+* K) (om oms : Fin m → K)
    (h : ∀ r r' : Fin m, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
      if r = r' then 1 else 0) (i j : Fin m) :
    ∑ k, σ^[2 * i.val] (om k) * σ^[2 * j.val] (oms k) = if i = j then 1 else 0 := by
  let M : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (om k)
  let Q : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (oms k)
  have hMQ : M.transpose * Q = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h r r',
      sum_zmod_val (fun n => if n % 2 = 0 then σ^[n] (om r * oms r') else 0), ← hd, sum_range_even,
      ← Fin.sum_univ_eq_sum_range (fun i => σ^[2 * i] (om r * oms r'))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [iter_mul]
    rfl
  have hMQ' : M * Q.transpose = 1 := by
    have := congrArg Matrix.transpose (mul_eq_one_comm.1 hMQ)
    simpa [Matrix.transpose_mul] using this
  have := congrFun (congrFun hMQ' i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem sum_eq_ite {d : ℕ} [NeZero d] (σ : K →+* K) (om oms : Fin (d / 2) → K)
    (hT : TrDual d σ om oms) (s t : ZMod d) (hst : s.val % 2 = t.val % 2) :
    ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  obtain ⟨hc, h⟩ := hT
  rw [Fintype.card_fin] at hc
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  let i : Fin (d / 2) := ⟨s.val / 2, by omega⟩
  let j : Fin (d / 2) := ⟨t.val / 2, by omega⟩
  have E := even_case hc σ om oms h i j
  have hij : (i = j) ↔ (s = t) := by
    rw [Fin.ext_iff, ← (ZMod.val_injective d).eq_iff]
    simp only [i, j]
    omega
  rcases Nat.mod_two_eq_zero_or_one s.val with h0 | h1
  · have e1 : s.val = 2 * i.val := by simp only [i]; omega
    have e2 : t.val = 2 * j.val := by simp only [j]; omega
    rw [e1, e2, E]
    exact if_congr hij rfl rfl
  · have e1 : s.val = 2 * i.val + 1 := by simp only [i]; omega
    have e2 : t.val = 2 * j.val + 1 := by simp only [j]; omega
    simp_rw [e1, e2, Function.iterate_succ_apply', ← map_mul, ← map_sum, E]
    split_ifs with h3 h4 h4
    · exact map_one σ
    · exact absurd (hij.1 h3) h4
    · exact absurd (hij.2 h4) h3
    · exact map_zero σ

end GlobalTheory.TrDualExpand

namespace GlobalTheory.KerStd.HypCoord

theorem trDual_expand : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p),
    TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 :=
  fun _ _ _ σ om oms hT s t hst => GlobalTheory.TrDualExpand.sum_eq_ite σ om oms hT s t hst

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
section
noncomputable section

namespace GlobalTheory.SatBcZero

section Weyl

open Formalism.UG GlobalTheory.SatakeWeyl

theorem weyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) (α : Fin m → ℂ)
    (h : GU σ n → ℂ) (hh : h ∈ Hecke ℂ (KU σ n)) :
    (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      ∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α := by
  choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem coeff_symm : CoeffSwap ∧ CoeffNeg := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact ⟨GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets,
    GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht)⟩

end Weyl

theorem eq_of_invariant (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (hf : ∀ α : Fin m → ℂ, (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧
      ∀ i, f (Function.update α i (α i)⁻¹) = f α) (α α' : Fin m → ℂ)
    (h : Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) =
      Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹)) : f α = f α' := by
  classical
  have h2 := congrArg (Multiset.map (fun x : ℂ => s(x, x⁻¹))) h
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => s((γ i)⁻¹, γ i)) = fun i => s(γ i, (γ i)⁻¹) :=
    fun γ => funext fun i => Sym2.eq_swap
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => s(α i, (α i)⁻¹))
      = Finset.univ.val.map (fun i => s(α' i, (α' i)⁻¹)) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := GlobalTheory.exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    rcases Sym2.eq_iff.1 (hπ i) with h4 | h4
    · exact Or.inl h4.1.symm
    · exact Or.inr h4.2.symm
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf (fun i => if i ∈ s then α' i else (α ∘ π) i)).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α).1 π, ← this]

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ,
      Formalism.MainNotions.N.ubc n (Finset.univ.val.map α) = Formalism.MainNotions.N.ubc n (Finset.univ.val.map α') →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  intro K _ _ _ ϖ σ q n hU α α' e φ hφ
  unfold Formalism.MainNotions.N.ubc at e
  have e1 := add_right_cancel e
  refine eq_of_invariant _ (Formalism.UG.SatU ϖ q φ)
    (fun γ => weyl_of_coeff coeff_symm.1 coeff_symm.2 K ϖ σ q n (n / 2) hU (by omega) (by omega) γ φ hφ) _ _ ?_
  simpa only [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBcZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEqStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  first | exact @GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | exact GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | (intros; apply GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq <;> assumption)
end

