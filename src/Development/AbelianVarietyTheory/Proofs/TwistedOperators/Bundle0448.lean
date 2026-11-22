import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilKernelFunctional_superposition_isTame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T), Measurable c → Continuous g → Continuous h → Continuous w → (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) → (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧ Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  first | exact @GlobalTheory.KerTame.kernel_tame | exact GlobalTheory.KerTame.kernel_tame | (intros; apply GlobalTheory.KerTame.kernel_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramifiedStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_fixes_latticeVacuum_nonsplit_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  first | exact @GlobalTheory.InertVac.om_fixes_latVac | exact GlobalTheory.InertVac.om_fixes_latVac | (intros; apply GlobalTheory.InertVac.om_fixes_latVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorKeepsLatticeVacuumOfTrivialAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.MoveVac

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_one_eq {D : D7} {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D T}
    (hg : projV T v g = 1) {u : WO S T} (hu : u ∈ latO S T (frameLat S) (frameLat T) fun w => w = v) :
    actO S T 1 g u = u := by
  have hid : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have hgA : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt T (.inl v) g = 1 := by
    show GlobalTheory.AdelicU.emb D.sp.cm.sig T.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g) = 1
    rw [show GlobalTheory.AdelicU.proj D.sp.cm.sig T.gram v g = 1 from hg, map_one]
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • Formalism.L2.Theta.mt T g =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    have h := GlobalTheory.PlaceComponent.mt_gAt T (.inl v) g
    rw [hgA, mt_one'] at h
    rw [eq_sub_of_add_eq h.symm, sub_smul, one_smul, sub_sub_cancel]
  have hu' : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) • u = u := GlobalTheory.InertVac.placeIdem_smul_eq hid hu
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one, ← hu', Matrix.mul_smul, ← Matrix.smul_mul, hm,
    Matrix.smul_mul, Matrix.one_mul]

theorem vacFin_om_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D T), projV T v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (1, g) f) := by
  intro D ψ S T χS χT om hW v g hg f hf
  obtain ⟨hth, hl1, hl2⟩ := hf
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h2 : 2 • u ∈ (latO S T (frameLat S) (frameLat T) fun w => w = v) := nsmul_mem hu 2
    rw [← actO_one_eq hg h2, ← hW.om_heis 1 g _ f hth, hl1 u hu]
  · rw [← actO_one_eq hg hu, ← hW.om_heis 1 g _ f hth, hl2 e he u hu hh]

end GlobalTheory.FinZeta.MoveVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplitStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_lattice_stabiliser_fixes_vacuum_nonsplit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  first | exact @GlobalTheory.VecInvInert.om_fixes_vacuum | exact GlobalTheory.VecInvInert.om_fixes_vacuum | (intros; apply GlobalTheory.VecInvInert.om_fixes_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.PureOm

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f₀ (base_theta hB)
  have hgen := GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨hp0, hploc⟩ := GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hstab := GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)
  have hgat := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1
  let Good : GA D S → GA D T → Prop := fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ),
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ),
      om (g * g', h * h') u = om (g, h) (om (g', h') u) := fun g g' h h' u => by
    have : om (g * g', h * h') = om (g, h) * om (g', h') := map_mul om (g, h) (g', h')
    rw [this]; rfl
  have G1 : Good 1 1 := fun x f hx => by
    simpa only [gAt_one, om1] using hx
  have Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h') := fun g h g' h' a b x f hx => by
    simpa only [gAt_mul, omm] using a _ _ (b x f hx)
  have Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h := fun q g h hg hh => by
    have e1 : ∀ p, p ≠ q → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact (hgat S q g).2.2 p hp
    have e2 : ∀ p, p ≠ q → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact (hgat T q h).2.2 p hp
    refine hgen g h ?_ ?_
    · refine (Set.finite_singleton q).subset fun p hp => ?_
      by_contra hpq
      exact hp (by rw [e1 p hpq, e2 p hpq, om1])
    · have := hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _)
        (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])
      have e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀ := by rw [gAt_inv, gAt_inv, hg, hh]
      simp only [e] at this
      exact this
  have Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) →
      (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h := fun g h hg hh => by
    refine hgen g h ?_ ?_
    · refine Set.finite_empty.subset fun p hp => ?_
      exact hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)
    · have e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀ := funext fun p => by
        rw [gAt_inv, gAt_inv]
        exact hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)
      rw [e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]
      exact hp0
  have GS : ∀ g, Good g 1 := fun g => by
    have hg : g ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      rcases hg with ⟨q, hq⟩ | hg
      · exact Gloc q g 1 hq (gAt_one T q)
      · exact Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  have GT : ∀ h, Good 1 h := fun h => by
    have hh : h ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h
    induction hh using Submonoid.closure_induction with
    | mem h hh =>
      rcases hh with ⟨q, hq⟩ | hh
      · exact Gloc q 1 h (gAt_one S q) hq
      · exact Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  intro x f hx g h
  have := Gmul _ _ _ _ (GS g) (GT h)
  rw [mul_one, one_mul] at this
  exact this x f hx

end GlobalTheory.PlaceTensor.PureOm
end

