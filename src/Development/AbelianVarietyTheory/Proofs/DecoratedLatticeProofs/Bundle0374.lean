import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairFiniteAdeleZeroMulPairFiniteAdeleZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdHomOrth

variable {D : D7}

def finInt (D : D7) : AddSubgroup (AE D) :=
  AddSubgroup.closure {z | ∃ α ∈ intAf D.host.F, ∃ x : D.host.E, IsIntegral ℤ x ∧ z = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x}

theorem gen_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] x : AE D) ∈ finInt D :=
  AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩

theorem star_int {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem incA_eq (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra D.host.F R] (a : R) (e : D.host.E) :
    Algebra.trace R (R ⊗[D.host.F] D.host.E) (a ⊗ₜ[D.host.F] e) =
      a * algebraMap D.host.F R (Algebra.trace D.host.F D.host.E e) := by
  have h1 : a ⊗ₜ[D.host.F] e = a • ((1 : R) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul R (R ⊗[D.host.F] D.host.E) ((1 : R) ⊗ₜ[D.host.F] e) =
      (Algebra.lmul D.host.F D.host.E e).baseChange R := by
    ext x
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem intAf_mul' {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) : a * b ∈ intAf D.host.F :=
  fun w => by rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem coe_mem_intAf (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  intro v
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 D.host.F) D.host.F v r

theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    ψ (pairA D.host.F 0 β) = 1 := by
  have := GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 1 (fun a => by
    have htr : Algebra.trace ℚ D.host.F (a : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) a : ℤ) : ℚ) :=
      (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) a).symm
    rw [mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _) β hβ
  rwa [map_one, mul_one] at this

theorem pairFiniteAdele_zero_mul_pairFiniteAdele_zero (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl

theorem pairFiniteAdele_zero_mul_algebraMap_base (α : Af D.host.F) (q : D.host.F) :
    pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) q =
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) q) :=
  Prod.ext (zero_mul (algebraMap D.host.F (Ainf D.host.F) q)) rfl

theorem incA_mul_mem {e : D.host.E} (he : IsIntegral ℤ e) {z : AE D} (hz : z ∈ finInt D) : incA D e * z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα (he.mul hx)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem cA_mem {z : AE D} (hz : z ∈ finInt D) : cA D z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [cA_tmul]
    exact gen_mem hα (star_int hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_mem' {z w : AE D} (hz : z ∈ finInt D) (hw : w ∈ finInt D) : z * w ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, x', hx', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairFiniteAdele_zero_mul_pairFiniteAdele_zero]
      exact gen_mem (intAf_mul' hα hβ) (hx.mul hx')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem psi_trace {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : AE D} (hz : z ∈ finInt D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E x) := Algebra.isIntegral_trace hx
    rw [trace_tmul, pairFiniteAdele_zero_mul_algebraMap_base]
    exact char_int hψ (intAf_mul' hα (coe_mem_intAf ⟨_, hint⟩))
  | zero => rw [map_zero]; exact AddChar.map_zero_eq_one ψ
  | add x y _ _ hx hy => rw [map_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx => rw [map_neg, AddChar.map_neg_eq_inv, hx, inv_one]

theorem exists_den {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, IsIntegral ℤ ((d : D.host.E) * f i) := by
  haveI : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).2 inferInstance
  obtain ⟨y, hy, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (f i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rw [zsmul_eq_mul] at h1
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h1; simpa using h1
  · rw [e] at h1
    have := h1.neg
    simpa using this

theorem exists_den_entries (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s, (d : AE D) * v r s ∈ finInt D := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hx0⟩ := exists_den (D := D) fun _ : Unit => ((a0 : D.host.E))⁻¹
  obtain ⟨e, he, hG⟩ := exists_den (D := D) fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2
  refine ⟨d * e, Nat.mul_pos hd he, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        have h2 : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E y) := y.2
        rw [hy, Algebra.smul_def] at h2
        exact h2
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((e : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul (star_int (hs k)) (hG (k, c))
      have e1 : ((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) = (e : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * e * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e1]
      exact (((hx0 ()).mul hA).mul (ht r)).mul hsum
    rw [Matrix.of_apply, ← map_natCast (incA D) (d * e), incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα hint'
  | zero => intro r s; rw [Matrix.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, mul_neg]; exact neg_mem (hx r s)

theorem exists_nsmul_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∃ M : ℕ, 0 < M ∧ ∀ x ∈ stdHom S T, ∀ w ∈ stdHom S T, ψ (symplO S T x (M • w)) = 1 := by
  intro D ψ hψ S T
  obtain ⟨d, hd, hden⟩ := exists_den_entries S T
  obtain ⟨p, hp, hξ⟩ := exists_den (D := D) fun _ : Unit => D.host.xi0
  obtain ⟨q, hq, hS⟩ := exists_den (D := D) fun i : Fin S.rank × Fin S.rank => S.gram⁻¹ i.1 i.2
  obtain ⟨r, hr, hT⟩ := exists_den (D := D) fun i : Fin T.rank × Fin T.rank => T.gram i.1 i.2
  refine ⟨p * q * r * d * d, by positivity, fun x hx w hw => ?_⟩
  refine psi_trace hψ ?_
  unfold hO
  simp only [Finset.mul_sum]
  refine sum_mem fun a _ => sum_mem fun b _ => sum_mem fun c _ => sum_mem fun e _ => ?_
  have key : incA D D.host.xi0 * (incA D (S.gram⁻¹ a b) * cA D (((p * q * r * d * d) • w) c b) * incA D (T.gram c e) * x e a) =
      incA D ((p : D.host.E) * D.host.xi0) * (incA D ((q : D.host.E) * S.gram⁻¹ a b) * (incA D ((r : D.host.E) * T.gram c e) *
        (cA D ((d : AE D) * w c b) * ((d : AE D) * x e a)))) := by
    rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [key]
  exact incA_mul_mem (hξ ()) (incA_mul_mem (hS (a, b)) (incA_mul_mem (hT (c, e))
    (mul_mem' (cA_mem (hden w hw c b)) (hden x hx e a))))

end GlobalTheory.StdHomOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealEqualityOfColumnsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_equality_of_columns : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.ColOK → RealEq f.t := by
  first | exact @GlobalTheory.Fam.realEq_of_colOK | exact GlobalTheory.Fam.realEq_of_colOK | (intros; apply GlobalTheory.Fam.realEq_of_colOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOfSupportedAtOrthogonalSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  first | exact @GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt | exact GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt | (intros; apply GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelOfLinks
section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop

theorem rel_of_links : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), ∀ u (f : FamCh W u) (d : BotDat W u), (∀ t, (f.t t).Is) → MainX f.t → LinkZero f d → LinkTail f → LinkDown f → LinkOnto f → LinkComm f → RatioQ f → ServedQ W → ∃ (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ), 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ UnitC W c ∧ d.Rel U c := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hIs hMain hZ hTail hDown hOnto hComm hRat hServ
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨n, hn⟩ : ∃ n, 2 * n + 2 = D.R.m := ⟨a - 1, by omega⟩
  have h : 2 * n + 2 * 0 + 2 = D.R.m := by omega
  have h₀ : 0 + 2 * n + 2 = D.R.m := by omega
  have hN : 2 * (n + 1) = D.R.m := by omega
  obtain ⟨S, r, s, hr, hS, hs, hcomm⟩ := hComm (n + 1) hN
  have hBot : ∀ t, (f.t t).cBot ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hIs t).cI j (Finset.mem_range.mp hj))
  have hTop : ∀ t, (f.t t).cTop (n + 1) ≠ 0 := fun t => (hRat (n + 1) hN t).1
  refine ⟨(S.symm : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u), r⁻¹, fun t => (f.t t).cTop (n + 1) * s / (f.t t).cBot,
    inv_pos.mpr hr, ?_, ?_, ?_⟩
  · intro φ
    have e := hS (S.symm φ)
    simp only [LinearEquiv.apply_symm_apply] at e
    simp only [LinearEquiv.coe_coe]
    rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

  · refine ⟨fun t => div_ne_zero (mul_ne_zero (hTop t) hs) (hBot t), ?_⟩
    intro w k hk
    refine GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio D.what₂.LL D.what₂.embLL w (qPrime W (W.Q.Rl.mu w)) _ _ (hRat (n + 1) hN (W.Q.Rl.mu w)).2
      (fun p hp hb => hServ w p hp hb) k ?_
    rw [hk]
    have a1 := hTop (W.Q.Rl.mu w)
    have a2 := hTop W.P.A3.A.μ0
    have b1 := hBot (W.Q.Rl.mu w)
    have b2 := hBot W.P.A3.A.μ0
    field_simp

  · intro T hT0
    obtain ⟨G₀, hG₀⟩ := hOnto n h T hT0
    refine ⟨fun φ₀ => (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
      ((f.t W.P.A3.A.μ0).up (n + 1) (col0 f W.P.A3.A.μ0 (S.symm φ₀))) G₀ / (f.t W.P.A3.A.μ0).cBot, ?_⟩
    intro φ₀ φ t F F' hFF α α' hrel y v
    obtain ⟨G, hG1, hGd⟩ := hDown n h t F'
    let sB : Bool → W.P.T := fun b => Bool.rec t W.P.A3.A.μ0 b
    let xB : Bool → D.what₂.Mu u := fun b => Bool.rec (S.symm φ) (S.symm φ₀) b
    let aB : Bool → ℂ := fun b => Bool.rec (α' / (f.t t).cBot) (α / (f.t W.P.A3.A.μ0).cBot) b
    let FB : ∀ b, (f.t (sB b)).CT := fun b => Bool.rec (motive := fun b => (f.t (sB b)).CT) G G₀ b
    have key := hMain n h h₀ Bool sB aB (fun b => col0 f (sB b) (xB b)) FB
      (fun b => ((hZ n h₀ (sB b) (xB b)).1))
    rw [Fintype.sum_bool] at key
    have top : aB true * (f.t (sB true)).cTop (n + 1) * (f.t (sB true)).tail (2 * (n + 1)) h
          ((f.t (sB true)).up (n + 1) (col0 f (sB true) (xB true))) (FB true) +
        aB false * (f.t (sB false)).cTop (n + 1) * (f.t (sB false)).tail (2 * (n + 1)) h
          ((f.t (sB false)).up (n + 1) (col0 f (sB false) (xB false))) (FB false) = 0 := by
      have e1 := hcomm t (S.symm φ) G
      rw [LinearEquiv.apply_symm_apply] at e1
      have e2 := hTail (n + 1) hN t φ F F' hFF G hG1
      change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
          ((f.t W.P.A3.A.μ0).up (n + 1) (col0 f W.P.A3.A.μ0 (S.symm φ₀))) G₀ +
        α' / (f.t t).cBot * (f.t t).cTop (n + 1) * (f.t t).tail (2 * (n + 1)) hN ((f.t t).up (n + 1) (col0 f t (S.symm φ))) G = 0
      rw [e1, e2]
      beta_reduce at hrel
      linear_combination hrel
    have bot := key top y v
    rw [Fintype.sum_bool] at bot
    have z1 := (hZ n h₀ W.P.A3.A.μ0 (S.symm φ₀)).2
      ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v
    have z2 := (hZ n h₀ t (S.symm φ)).2 ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v
    change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).per 0 n h₀ (col0 f W.P.A3.A.μ0 (S.symm φ₀))
        ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v +
      α' / (f.t t).cBot * (f.t t).cBot * (f.t t).per 0 n h₀ (col0 f t (S.symm φ))
        ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v = 0 at bot
    rw [z1, z2] at bot
    have d1 : ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)).1 = T := hG₀
    have d2 : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = rowAt W t F' := hGd
    rw [d1, d2, div_mul_cancel₀ _ (hBot _), div_mul_cancel₀ _ (hBot _)] at bot
    simpa only [LinearEquiv.coe_coe] using bot

end GlobalTheory.MiTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem levFn_datY_noQ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm) (x : GL (Fin V.rank) (Lev.EAf D)) :
    levFn β (Lev.datY V.rank r t j hr Pg Q P χ ξ fr) x = levFn β (Lev.datY V.rank r t j hr Pg ∅ P χ ξ' fr) x := by
  unfold levFn
  have hq : ∀ PP ∈ (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).Q,
      (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).xq PP
        (dBlk (blk2 (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r = r from rfl, Formalism.IndefR.Eqv.Act.block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem levS_datYt_base (W : RealPack ex) :
    levS (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) = levS (Yc D 0) ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
  have e : Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) =
      Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
    refine Subgroup.ext fun x => ?_
    show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
    unfold LevCh.datYt LevCh.dat0
    rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (pk W).Pg
      ((pk W).Q W.P.A3.A.μ0) (lvP W) (pk W).chi ((pk W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B x]
    rfl
  unfold levS Lev.levG
  rw [e]

theorem levChi_datYt_base (W : RealPack ex) :
    Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) =
      Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
  funext k
  unfold Lev.levChi LevCh.datYt LevCh.dat0
  rw [levFn_datY_noQ ((pk W).βY 0) Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (pk W).Pg
      ((pk W).Q W.P.A3.A.μ0) (lvP W) (pk W).chi ((pk W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B]

theorem rows_mem_CC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ T ∈ ThetaLiftSpaceZero W, T ∈ (GlobalTheory.BaseChain.stageY W 0).CC (GlobalTheory.BaseChain.com W) := by
  intro D L hT Gi Gl Kc Yd cX ex W _ T hT0
  show T ∈ MultT (pk W).θ ((pk W).MY 0) (levS (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)))
    (Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)))
  rw [levS_datYt_base W, levChi_datYt_base W]
  exact hT0

end GlobalTheory.BaseChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutes
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW

theorem hMat_mem_hfin_comm : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  intro D X u c h hef hz hh
  have hfixV : ∀ v ∈ fixSet X u, GlobalTheory.ScalW.prj X u (incl X.B.I v) = incl X.B.I v := by
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv)
    · exact (hef a).1
    · exact (hef a).2
    · rw [Set.mem_singleton_iff.1 hv]; exact hz
  have hmem : h ∈ Hfin X u := by
    intro v hv
    show X.B.I.fmat h *ᵥ incl X.B.I v = incl X.B.I v
    rw [hh, hMat_mulVec, hfixV v hv, ← add_smul, add_sub_cancel, one_smul]
  refine ⟨hmem, fun h' hh' => ?_⟩
  have hg : ∀ v ∈ fixSet X u, X.B.I.fmat h' *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u ⟨h', hh'⟩
  have hgi : ∀ v ∈ fixSet X u, X.B.I.fmat h'⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix_inv X u ⟨h', hh'⟩
  have hE := Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u
  have hF := Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix X u
  have hZ := Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u
  have hmv : ∀ v, v ∈ fixSet X u → ∀ y, hA X.B.I (incl X.B.I v) (X.B.I.fmat h' *ᵥ y) = hA X.B.I (incl X.B.I v) y := by
    intro v hv y
    rw [GlobalTheory.St.G.FrameClose.hA_move, hgi v hv]
  have hprj : ∀ y, prj X u (X.B.I.fmat h' *ᵥ y) = prj X u y := by
    intro y
    simp only [prj, eV, fV, zV, hmv _ (hE _), hmv _ (hF _), hmv _ hZ]
  have hprj2 : ∀ y, X.B.I.fmat h' *ᵥ prj X u y = prj X u y := by
    intro y
    simp only [prj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, eV, fV, zV,
      hg _ (hE _), hg _ (hF _), hg _ hZ]
  have hM : X.B.I.fmat (h * h') = X.B.I.fmat (h' * h) := by
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, hh]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMat_mulVec, hMat_mulVec, hprj, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hprj2]
  exact Subtype.ext (Units.ext hM)

end GlobalTheory.ScalW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem sdY_frames {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) :
    PkHyp W → ∀ j, j < D.R.m → IsSelfDualC (Yc D j) ((pk W).ΛY j) ∧ Formalism.L2.DIV.IsFrame ((pk W).βY j) ((pk W).ΛY j) := by
  intro h j hj
  have hL := h.bot.hyp.2.2.2.1.lev.βY j hj
  refine ⟨GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL, ?_⟩
  obtain ⟨c, hc⟩ := hL
  exact hc.1

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ServedQOfBot
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem servedQ_of_bot : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → RealRec W.Q → ServedQ W := by
  intro D L hT Gi Gl Kc Yd cX ex W _ _
  exact served_holds W

end GlobalTheory.MiTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_pair_along_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ ∧ I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ ∀ j, j ≤ B.R.m → ∀ g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j), ∃ x, IsDetRoot _ g x := by
  first | exact @GlobalTheory.AdForm.StdSteps.stdPair_steps | exact GlobalTheory.AdForm.StdSteps.stdPair_steps | (intros; apply GlobalTheory.AdForm.StdSteps.stdPair_steps <;> assumption)
end

