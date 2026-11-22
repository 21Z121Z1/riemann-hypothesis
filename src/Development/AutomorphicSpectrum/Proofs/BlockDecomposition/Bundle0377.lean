import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNatural
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.CompanionTheory.SegFine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {n : ℕ}

abbrev ev (k : Type) [Field k] (n : ℕ) : (∀ _ : Fin 1, GL (Fin n) k) →* GL (Fin n) k :=
  Pi.evalMonoidHom (fun _ : Fin 1 => GL (Fin n) k) 0

abbrev lv (τ : Representation ℂ (GL (Fin n) k) X) : Representation ℂ (∀ _ : Fin 1, GL (Fin n) k) X := τ.comp (ev k n)

theorem stdBlocks_one (h : ∑ _ : Fin 1, n = n) (a : Fin 1) (i : Fin n) :
    stdBlocks (fun _ : Fin 1 => n) h ⟨a, i⟩ = i :=
  Fin.ext (by rw [stdBlocks_val, Subsingleton.elim a 0]; simp)

theorem leviEmb_one (h : ∑ _ : Fin 1, n = n) (g : ∀ _ : Fin 1, GL (Fin n) k) :
    leviEmb k (stdBlocks (fun _ : Fin 1 => n) h) g = g 0 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := leviEmb_apply_same k (stdBlocks (fun _ : Fin 1 => n) h) g 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

theorem unipRad_one (h : ∑ _ : Fin 1, n = n) : unipRad k (stdBlocks (fun _ : Fin 1 => n) h) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => Units.ext (Matrix.ext fun i j => ?_)
  have := (mem_unipRad.1 hu).2 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

def jacEquiv (h : ∑ _ : Fin 1, n = n) (π : Representation ℂ (GL (Fin n) k) V) :
    (lv π).Equiv (jac (stdBlocks (fun _ : Fin 1 => n) h) π) := by
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 = ⊥ := by
    rw [unipRad_one]
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp
  have hd : ∀ g, deltaHalf k (fun _ : Fin 1 => Fin n) g = 1 := fun g => by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  let f : (lv π).IntertwiningMap (jac (stdBlocks (fun _ : Fin 1 => n) h) π) :=
    ⟨(twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1).mkQ, fun g => LinearMap.ext fun v => by
      show Submodule.Quotient.mk (π (g 0) v) = jac _ π g (Submodule.Quotient.mk v)
      rw [jac_mk, hd, leviEmb_one]
      simp⟩
  refine equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, Submodule.Quotient.mk_surjective _⟩
  have : v ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  rw [hK] at this
  exact this

def piTensorEquiv (τ : Representation ℂ (GL (Fin n) k) X) :
    (lv τ).Equiv (piTensor fun _ : Fin 1 => τ) := by
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => X) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  let f : (lv τ).IntertwiningMap (piTensor fun _ : Fin 1 => τ) :=
    ⟨L.toLinearMap, fun g => LinearMap.ext fun v => by
      show L (τ (g 0) v) = piTensor (fun _ : Fin 1 => τ) g (L v)
      rw [hL, hL, piTensor_tprod]
      exact congrArg _ (funext fun a => by rw [Subsingleton.elim a 0])⟩
  exact equivOfBijective f L.bijective

def subrepComp (τ : Representation ℂ (GL (Fin n) k) X) :
    Subrepresentation (lv τ) ≃o Subrepresentation τ where
  toFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (fun _ => g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (g 0) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {τ : Representation ℂ (GL (Fin n) k) X} (h : τ.IsIrreducible) :
    (lv τ).IsIrreducible := (subrepComp τ).isSimpleOrder_iff.2 h

theorem jhMult_one (h : ∑ _ : Fin 1, n = n) (τ : Representation ℂ (GL (Fin n) k) X)
    (π : Representation ℂ (GL (Fin n) k) V) :
    jhMult (piTensor fun _ : Fin 1 => τ) (jac (stdBlocks (fun _ : Fin 1 => n) h) π) =
      jhMult (lv τ) (lv π) := by
  rw [← jhMult_congr_left (piTensorEquiv τ), ← jhMult_congr_right _ (jacEquiv h π)]

theorem jm_eq_one (x : IrrGL k) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL k) (hy : ∑ a, (y a).1 = x.1) (hyx : y = fun _ => x) : jm y hy π = 1 := by
  subst hyx
  refine (jhMult_one hy x.rep π).trans ?_
  rw [jhMult_congr_right _ (compEquiv φ (ev k x.1))]
  exact jhMult_self (isIrreducible_comp x.2.rep.irr)

theorem eq_of_one_le_jm (x : IrrGL k) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL k) (hy : ∑ a, (y a).1 = x.1) (h : 1 ≤ jm y hy π) : y 0 = x := by
  obtain ⟨z, rfl⟩ : ∃ z, y = fun _ => z := ⟨y 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨d, c⟩ := z
  obtain ⟨m, b⟩ := x
  obtain rfl : d = m := by simpa using hy
  have h0 : jhMult (lv c.rep.ρ) (lv π) ≠ 0 := by
    rw [← jhMult_one hy]
    exact ENat.one_le_iff_ne_zero.1 h
  have hπ : π.IsIrreducible := isIrreducible_of_equiv φ.symm b.rep.irr
  obtain ⟨E⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv (isIrreducible_comp c.rep.irr) (isIrreducible_comp hπ)
  let f : π.IntertwiningMap c.rep.ρ := ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun v =>
    E.toIntertwiningMap.isIntertwining _ _ (fun _ => g) v⟩
  have E' : c.rep.ρ.Equiv b.rep.ρ := (equivOfBijective f E.toLinearEquiv.bijective).symm.trans φ
  exact congrArg (Sigma.mk d) (irrCl_eq_iff.2 ⟨E'⟩)

theorem dec_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : dec (Segment.single ρ hρ) = fun _ => ρ := funext fun a => by
  show ρ.nu (((Fin.rev (a : Fin 1) : Fin 1) : ℕ) : ℂ) = ρ
  simp [Fin.val_eq_zero]

theorem not_one_le_jm {N c : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsCuspidal π)
    (y : Fin (c + 2) → IrrGL k) (hy : ∑ a, (y a).1 = N) (hc : ∀ a, (y a).IsCusp) : ¬ 1 ≤ jm y hy π := by
  intro h
  have hne : unipRad k (stdBlocks (fun a => (y a).1) hy) ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2
    ⟨stdBlocks (fun a => (y a).1) hy ⟨0, ⟨0, (hc 0).1⟩⟩, stdBlocks (fun a => (y a).1) hy ⟨1, ⟨0, (hc 1).1⟩⟩, by simp⟩
  have := hπ.2 _ _ _ hne
  have hn : Nontrivial (PiTensorProduct ℂ fun a => (y a).2.rep.V) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ fun a => Model.nontrivial_of_isIrreducible (y a).2.rep.irr
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h)
  exact not_subsingleton _ hf.subsingleton

theorem fineJac_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJac Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  obtain rfl : ρ.1 = N := by
    have := hπ.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique hπ
  refine ⟨fun hd => jm_eq_one ρ π φ _ hd (dec_single ρ hρ), fun c y hy hc h1 => ?_⟩
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL k) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (dec_single ρ hρ) _).symm⟩
  · exact absurd h1 (not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

end GlobalTheory.CompanionTheory.SegFine

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FrobInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mk_parab (e : (Σ a, m a) ≃ n) (τ : Representation ℂ (GL n k) V) (p : parab k e) (w : V) :
    (Submodule.Quotient.mk (τ (p : GL n k) w) : Jacquet τ (unipRad k e)) =
      Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) w) := by
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
  have key : ∀ y : V, (Submodule.Quotient.mk (τ u y) : Jacquet τ (unipRad k e)) = Submodule.Quotient.mk y := by
    intro y
    rw [Submodule.Quotient.eq]
    apply Submodule.subset_span
    refine Set.mem_ofPred.mpr ⟨⟨u, hu⟩, y, ?_⟩
    simp
  have hL : ∀ y : V, (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) y) : Jacquet τ (unipRad k e)) =
      ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • jac e τ (leviProj k e p) (Submodule.Quotient.mk y) := by
    intro y
    rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
  have e1 : τ (p : GL n k) w = τ (leviEmb k e (leviProj k e p)) (τ u w) := by
    first
    | (rw [hp, map_mul]; rfl)
    | rw [hp, map_mul]
  rw [e1, hL, hL, key]

def frobFun (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) : GL n k → W :=
  fun g => f (Submodule.Quotient.mk (τ g v))

theorem frobFun_law (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (p : parab k e) (g : GL n k) :
    frobFun e f v (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (frobFun e f v g) := by
  have h1 : frobFun e f v (p * g) =
      f (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) := by
    show f (Submodule.Quotient.mk (τ ((p : GL n k) * g) v)) = _
    rw [map_mul]
    exact congrArg f (mk_parab e τ p (τ g v))
  have h2 := LinearMap.congr_fun (f.isIntertwining' (leviProj k e p)) (Submodule.Quotient.mk (τ g v))
  simp only [LinearMap.comp_apply] at h2
  rw [h1]
  show f.toLinearMap (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) =
    ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • ρ (leviProj k e p) (f.toLinearMap (Submodule.Quotient.mk (τ g v)))
  rw [← h2, jac_mk, map_smul, smul_smul, Units.mul_inv, one_smul]

theorem frobFun_mem (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    frobFun e f v ∈ indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) := by
  show ∀ (h : ↥(parab k e)) (g : GL n k),
    frobFun e f v (↑h * g) = ((twist ρ (deltaHalf k m)).comp (leviProj k e)) h (frobFun e f v g)
  intro p x
  rw [frobFun_law, MonoidHom.comp_apply, twist_apply]

theorem frobFun_translate (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (jac e τ).IntertwiningMap ρ) (v : V) (h x : GL n k) :
    frobFun e f v (x * h) = frobFun e f (τ h v) x := by
  show f (Submodule.Quotient.mk (τ (x * h) v)) = f (Submodule.Quotient.mk (τ x (τ h v)))
  first
  | (rw [map_mul]; rfl)
  | rw [map_mul]

theorem frobFun_smooth (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (⟨frobFun e f v, frobFun_mem e f v⟩ : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) ∈
      smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) := by
  show IsOpen {g : GL n k | (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))) g
    ⟨frobFun e f v, frobFun_mem e f v⟩ = ⟨frobFun e f v, frobFun_mem e f v⟩}
  set F : indSpace (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) :=
    ⟨frobFun e f v, frobFun_mem e f v⟩ with hF
  set R := ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) with hR
  have hstab : ∀ s, τ s v = v → R s F = F := by
    intro s hs
    apply Subtype.ext
    funext x
    show frobFun e f v (x * s) = frobFun e f v x
    rw [frobFun_translate, hs]
  rw [isOpen_iff_forall_mem_open]
  intro g0 hg0
  refine ⟨(fun g => g0⁻¹ * g) ⁻¹' {g | τ g v = v}, ?_, IsOpen.preimage (continuous_const_mul g0⁻¹) (hτ v), ?_⟩
  · intro g hg
    have h1 : R (g0 * (g0⁻¹ * g)) F = R g0 (R (g0⁻¹ * g) F) := by
      first
      | (rw [map_mul]; rfl)
      | rw [map_mul]
    rw [mul_inv_cancel_left] at h1
    show R g F = F
    rw [h1, hstab _ hg]
    exact hg0
  · show τ (g0⁻¹ * g0) v = v
    rw [inv_mul_cancel, map_one]
    rfl

def frobInv (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (parInd e ρ) where
  toLinearMap :=
    { toFun := fun v => ⟨⟨frobFun e f v, frobFun_mem e f v⟩, frobFun_smooth e hτ f v⟩
      map_add' := fun v w => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (v + w))) = f (Submodule.Quotient.mk (τ g v)) + f (Submodule.Quotient.mk (τ g w))
        rw [map_add, Submodule.Quotient.mk_add, map_add]
      map_smul' := fun c v => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (c • v))) = c • f (Submodule.Quotient.mk (τ g v))
        rw [map_smul, Submodule.Quotient.mk_smul, map_smul] }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (frobFun_translate e f v g x).symm

theorem frobInv_one (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (v : V) :
    (frobInv e hτ f v).1.1 1 = f (Submodule.Quotient.mk v) := by
  show f (Submodule.Quotient.mk (τ 1 v)) = f (Submodule.Quotient.mk v)
  first
  | (rw [map_one]; rfl)
  | rw [map_one]

theorem exists_frobInv_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (jac e τ).IntertwiningMap ρ) (hf : ∃ v, f v ≠ 0) :
    ∃ v, frobInv e hτ f v ≠ 0 := by
  obtain ⟨w, hw⟩ := hf
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨v, fun h => hw ?_⟩
  have h1 := frobInv_one e hτ f v
  rw [h] at h1
  exact h1.symm

theorem exists_map_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ)
    (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep))
    (hf : ∃ v, f v ≠ 0) : ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  exact ⟨frobInv (stdBlocks (fun a => (x a).1) hd) hτ f, exists_frobInv_ne_zero _ hτ f hf⟩

end GlobalTheory.CompanionTheory.FrobInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMassStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_weight_total_mass : ∀ (d : ℕ) (α : Type) [Fintype α], ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibSim

theorem conj_scal {A : Type} [CommRing A] {M n : ℕ} (C : Matrix (Fin n) (Fin M) A)
    (D : Matrix (Fin M) (Fin n) A) (G' G J : Matrix (Fin M) (Fin M) A) (t : A)
    (h : G' * J * G = t • J) : (C * G' * J) * (G * D) = t • (C * J * D) := by
  calc (C * G' * J) * (G * D) = C * (G' * J * G) * D := by simp only [Matrix.mul_assoc]
    _ = t • (C * J * D) := by rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem fib_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g l hl hgl a c hmu hnu S
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  obtain ⟨u, rfl⟩ := hl
  let am := algebraMap R (R ⊗[F] E)
  have hinv : ∀ (v w : Rˣ) (_ : (v : R) * w = 1) (A : HermR R σ n),
      GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (w : R) A) = A := by
    intro v w hvw A
    apply Subtype.ext
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, smul_smul, ← map_mul, hvw,
      map_one, one_smul]
  have hcs : ∀ v : R, Continuous (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ v : HermR R σ n → HermR R σ n) := by
    intro v
    have hv : Continuous fun A : HermR R σ n => (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    exact (hv.const_smul (algebraMap R (R ⊗[F] E) v)).subtype_mk _
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R)
      invFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ ((u⁻¹ : Rˣ) : R)
      left_inv := hinv _ _ (by simp)
      right_inv := hinv _ _ (by simp)
      continuous_toFun := hcs _
      continuous_invFun := hcs _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ (v : Rˣ) (A : HermR R σ n), A ∈ B → GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A ∈ B := by
    intro v A hA
    show IsUnit ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, Matrix.det_smul]
    exact ((v.isUnit.map (algebraMap R (R ⊗[F] E))).pow _).mul hA
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact hdet _ _ hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hgram : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) =
      (algebraMap R (R ⊗[F] E) (u : R)) • gramR R σ J X := by
    intro X
    rw [GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.colM_actTup,
      cT_mul]
    exact conj_scal _ _ _ _ _ _ hgl
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (actTup R g X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R) (G X) : HermR R σ n) :
        Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, ← hGe]
    exact hgram X
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τh S)
  have hs : τh.symm (τh S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  exact huq.symm

end GlobalTheory.CompanionTheory.SW.FibSim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharactersStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_induced_two_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | exact GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | (intros; apply GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquareStatement
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | exact GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | (intros; apply GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_restriction_natural : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_glue | exact GlobalTheory.CompanionTheory.KunGlue.kun_glue | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_glue <;> assumption)
end

