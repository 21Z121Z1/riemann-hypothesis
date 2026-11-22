import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReads
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime]

theorem exists_read_map {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l])
    (r : Γ →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l])
    (hR : Reads ρ r b e) (L : FinExt l) (r' : Γ →* GL (Fin a) ↥L.1)
    (R : Representation ↥L.1 Γ (Fin a → ↥L.1)) (hRr : ∀ g v, R g v = (r' g).val *ᵥ v)
    (hr : ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) (v : Fin a → ↥L.1) :
    ∃ (F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : Fin d → ℚ_[l]),
      (∀ g y, F (qRep ρ g y) = R g (F y)) ∧ F x = v := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ↥L.1 (Om l))
    (LinearMap.ker_eq_bot.2 (algebraMap ↥L.1 (Om l)).injective)
  have hp' : ∀ c : ↥L.1, p (c : Om l) = c := fun c => LinearMap.congr_fun hp c
  let Φ : (Fin d → ℚ_[l]) → Matrix (Fin a) (Fin a) (Om l) := fun x => ∑ j, algebraMap ℚ_[l] (Om l) (x j) • b j
  let w : Fin a → Om l := fun k => (v k : Om l)
  have hΦs : ∀ (c : ℚ_[l]) x, Φ (c • x) = c • Φ x := by
    intro c x
    simp only [Φ, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, algebraMap_smul]
  have hΦa : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    simp only [Φ, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  let F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1) :=
    { toFun := fun x i => p ((Φ x *ᵥ w) i)
      map_add' := by
        intro x y; funext i
        simp only [hΦa, Matrix.add_mulVec, Pi.add_apply, map_add]
      map_smul' := by
        intro c x; funext i
        have h1 : ((Φ (c • x)) *ᵥ w) i = c • ((Φ x *ᵥ w) i) := by
          rw [hΦs]
          simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Matrix.smul_apply, smul_mul_assoc]
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [h1]
        exact LinearMap.map_smul_of_tower p c _ }
  have hq : ∀ g y, qRep ρ g y = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ y := fun g y => rfl
  have hΦg : ∀ g y, Φ (qRep ρ g y) = (r g).val * Φ y := by
    intro g y
    rw [hq]
    simp only [Φ, Matrix.mul_sum, Matrix.mul_smul, hR.equi, Finset.smul_sum, smul_smul]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨F, fun j => algebraMap ℤ_[l] ℚ_[l] (e j), fun g y => ?_, ?_⟩
  · funext i
    rw [hRr]
    change p ((Φ (qRep ρ g y) *ᵥ w) i) = ∑ k, (r' g).val i k * p ((Φ y *ᵥ w) k)
    rw [hΦg, ← Matrix.mulVec_mulVec]
    generalize Φ y *ᵥ w = z
    change p (∑ k, (r g).val i k * z k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hr]
    exact LinearMap.map_smul p ((r' g).val i k) (z k)
  · funext i
    change p ((Φ _ *ᵥ w) i) = v i
    have h1 : Φ (fun j => algebraMap ℤ_[l] ℚ_[l] (e j)) = 1 := hR.one
    rw [h1, Matrix.one_mulVec]
    exact hp' (v i)

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem crys_pass (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsCrys (P.PD K) ρq) : IsCrys (P.PD K) R := by
  haveI := L.2
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.TateDualCrys.fracInv_of_tied T K
  have hu := GlobalTheory.TateDualCrys.lineUnit_of_tied T K
  rw [GlobalTheory.RegularRing.isCrys_iff_span (P.PD K) hf hu] at h ⊢
  refine GlobalTheory.RegularRing.eq_top_of_tmul _ fun c v => ?_
  obtain ⟨F, x, hFe, rfl⟩ := hF v
  have hm : ∀ y ∈ DcrisK₀ (P.PD K) ρq, F.baseChange P.R.B y ∈ DcrisK₀ (P.PD K) R := by
    intro y hy
    rw [GlobalTheory.RegularRing.mem_DcrisK₀] at hy ⊢
    intro g
    have hc : ∀ z, F.baseChange P.R.B (GlobalTheory.RegularRing.sig (P.PD K) ρq g z) =
        GlobalTheory.RegularRing.sig (P.PD K) R g (F.baseChange P.R.B z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b w => simp [GlobalTheory.RegularRing.sig_tmul, hFe]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    rw [← hc, hy g]
  have h1 : Submodule.span P.R.B (DcrisK₀ (P.PD K) ρq : Set (P.R.B ⊗[ℚ_[l]] V)) ≤
      (Submodule.span P.R.B (DcrisK₀ (P.PD K) R : Set (P.R.B ⊗[ℚ_[l]] (Fin a → ↥L.1)))).comap
        (F.baseChange P.R.B) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (hm y hy)
  have h2 := h1 (h ▸ Submodule.mem_top : c ⊗ₜ[ℚ_[l]] x ∈ _)
  simpa using h2

theorem dr_pass (T : LocTied l P AI) (K L : FinExt l) {LL0 : Type} [Field LL0] [Algebra ℚ_[l] LL0]
    {V : Type} [AddCommGroup V] [Module LL0 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL0 V] {a : ℕ}
    (ρ0 : Representation LL0 ↥(GK K) V) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρ0 g y) = R g (F y)) ∧ F x = v)
    (h : GlobalTheory.DRFil.Spans (P.PD K) ρ0) : IsDR (P.PD K) R := by
  haveI := L.2
  apply GlobalTheory.DRFil.isDR_of_spans T K L R
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add y z hy hz =>
    obtain ⟨m, b, dd, hd, rfl⟩ := hy
    obtain ⟨m', b', dd', hd', rfl⟩ := hz
    refine ⟨m + m', Fin.append b b', Fin.append dd dd', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hd i
      · simpa using hd' i
    · rw [Fin.sum_univ_add]
      simp
  | tmul v c =>
    obtain ⟨F, x, hFe, rfl⟩ := hF v
    obtain ⟨m, b, dd, hd, hx⟩ := h (x ⊗ₜ[ℚ_[l]] c)
    let E : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR :=
      TensorProduct.map F (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    have hE : ∀ (β : P.R.BdR) z, E (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR LL0 V β z) =
        GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) β (E z) := by
      intro β z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    have hg : ∀ g z, E (actVdR (P.PD K) ρ0 g z) = actVdR (P.PD K) R g (E z) := by
      intro g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E, actVdR, hFe]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    refine ⟨m, b, fun i => E (dd i), fun i => ?_, ?_⟩
    · have h1 := hd i
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at h1 ⊢
      intro g
      rw [← hg, h1 g]
    · have h2 := congrArg E hx
      rw [map_sum] at h2
      simp only [hE] at h2
      simpa [E] using h2

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem dr_pass_rat (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsDR (P.PD K) ρq) : IsDR (P.PD K) R := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρq g, map_add' := (ρq g).map_add, map_smul' := fun x v => (ρq g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.BdR), actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρq g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.BdR, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρq := by
    intro x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(DdR (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(DdR (P.PD K) ρq) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' : IsDR (P.PD K) ρ' := by
    unfold IsDR at h ⊢
    rw [hfr, hfr, eq.finrank_eq, h]
  exact dr_pass T K L ρ' R hF ((GlobalTheory.DRFil.filSpans T K LL ρ' h').spans)

theorem isDR_isCrys_of_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a d ρ r b e hR L r' R _ hRr hr
  have hF := exists_read_map ρ r b e hR L r' R hRr hr
  exact ⟨dr_pass_rat T K L (qRep ρ) R hF, crys_pass T K L (qRep ρ) R hF⟩

end GlobalTheory.ReadPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCore
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TopDict

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem mk_mem_unr_iff {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (I : Subgroup G) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∃ b, ∀ g ∈ I, (z : G → M) g = π g b - b := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    refine ⟨b - b', fun g hg => ?_⟩
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg] at h1
    have h2 : (z : G → M) g = π g b - b - (π g b' - b') := by rw [h1]; abel
    rw [h2, map_sub]
    abel
  · rintro ⟨b, hb⟩
    exact ⟨z, ⟨b, hb⟩, rfl⟩

theorem admissibleExtension_iff_equivariantCoefIso {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ}
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
    {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (W : Representation O G M) (W' : Representation O G M') (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x))
    (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X)
    (hzz : ∀ g, z' g = LinearEquiv.rTensor X e (z g)) (hz : z ∈ Z1 (twCoef W χ X) ⊤)
    (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0) :
    Admissible PD emb Γ t Ut (Ea W χ hc ⟨z, hz⟩) ↔ Admissible PD emb Γ t Ut (Ea W' χ hc ⟨z', hz'⟩) := by
  obtain ⟨f, hf⟩ := (GlobalTheory.T.equivariantIso_transport_cocycles_extensions W W' e he χ X z z' hzz).2.1 hz hz' hc
  have hf' : ∀ g x, f.symm (Ea W' χ hc ⟨z', hz'⟩ g x) = Ea W χ hc ⟨z, hz⟩ g (f.symm x) :=
    fun g x => f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  exact ⟨fun h => h.of_equiv f hf, fun h => h.of_equiv f.symm hf'⟩

theorem WachMod_mem_B1_iff {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (z : G → M) : z ∈ B1 π ⊤ ↔ ∃ m, ∀ g, z g = π g m - m := by
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext fun g => (hm g).symm⟩

set_option maxHeartbeats 8000000 in

theorem topCore_of_typings : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P →
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)),
    Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  intro l _ P AI hT H hSA hSB hSC K LL hA lam hlam h5 t h w η typ U V _ _ _ _ _ _ _ _ _ _ _ ρ T₀ χ hyp X _ _ _
  let T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := LocLat.mk V ρ hyp.2.2.1 T₀
  have hcard := GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim P AI hT H K LL hA V ρ U hyp.2.2.2.1 hyp.2.2.2.2.1
  obtain ⟨r, D, ε, hHyp, hDt, hcount, hchi⟩ := GlobalTheory.T.exists_numerical_galoisData_localSituation P H K LL hA lam hlam h5 t h w η typ U T χ hyp hcard
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hHyp.1⟩
  let S : TopSit P := ⟨K, LL, _, r, (H.W K 1 LL hA.2.2).emb, D, ⟨lam, T, χ 1, ε⟩, hHyp⟩
  have hkill : ∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0 := by
    obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit (↥(OL LL)) lam hlam.not_isUnit X
  have hCl := GlobalTheory.AdmClosure.admissible_closed S
  obtain ⟨hL0, hLc⟩ := GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl (StdAdm.stdAdm S (CrysRules.crysCalc AI hT S) hCl)
  have hpoly : tableLineDegreeTwo.resPoly ρ χ t = tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t := by
    funext g
    change tableLineDegreeTwo.resPoly ρ χ t g = tableLineDegreeTwo.resPoly ρ S.Γ.chi D.t g
    rw [hDt]
    unfold tableLineDegreeTwo.resPoly
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hchi c hc]
  have key : ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T'.ρ) (z : S.G → ↥L.T ⊗[S.O] X)
      (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤),
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) L X (χ 1) z ↔
      ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) := by
    intro T' L z hz
    rw [hpoly]
    exact exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha =>
      GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext S (tableLineDegreeTwo.jTil U w t) hcount T' L X z hz a ha

  have ext_iff : ∀ (c : ℕ) {Mc : Type} [AddCommGroup Mc] [Module S.O Mc] (Wc : Representation S.O S.G Mc)
      (e : S.O ≃ₗ[S.O] Mc), (∀ g x, e (S.Γ.Wchi c g x) = Wc g (e x)) →
      ∀ (z₀ : S.G → S.O ⊗[S.O] X) (z : S.G → Mc ⊗[S.O] X), (∀ g, z g = LinearEquiv.rTensor X e (z₀ g)) →
      ∀ (hz₀ : z₀ ∈ Z1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤) (hz : z ∈ Z1 (twCoef Wc S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea Wc S.Γ.χ₁ ha ⟨z, hz⟩)) ↔
        (∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (S.Γ.Wchi c) S.Γ.χ₁ ha ⟨z₀, hz₀⟩))) := by
    intro c Mc _ _ Wc e he z₀ z hzz hz₀ hz
    refine exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha => ?_
    exact (admissibleExtension_iff_equivariantCoefIso (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut (S.Γ.Wchi c) Wc e he S.Γ.χ₁ X z₀ z hzz hz₀ hz ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' T₀' hρ' hTT z hz
    have hz' : z ∈ Z1 (twCoef (latRep T₀) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff T₀ X (χ 1)).2 z).1 hz
    rw [key T T₀ z hz', GlobalTheory.T.cocycle_class_admissible S S.Γ.W₀ X hkill (hL0 X).2.1 ⟨z, hz'⟩]
    have hA' := ((hSA K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2).2.2.2.2 X).2
    exact (Set.ext_iff.1 hA' (Submodule.Quotient.mk ⟨z, hz'⟩)).trans
      (SetLike.mem_coe.trans (GlobalTheory.T.period_data_dual_exact (P.PD K) T₀ ρ' T₀' X (χ 1) hρ' hTT z hz'))
  · intro c hc Lc z hz
    have hc' := Finset.mem_Icc.1 hc
    have hc1 : c ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨by omega, hc'.2⟩
    have hχc : S.Γ.chi c = χ c := hchi c hc1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ c) Lc
    have he' : ∀ g x, e (S.Γ.Wchi c g x) = latRep Lc g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, hB, -⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi c) (latRep Lc) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep Lc) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 c hc1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c))) (fun x => hcont.mul continuous_const) Lc
    rw [key Tc Lc z hz', ext_iff c (latRep Lc) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi c) X hkill ((hLc c (by omega) (by rw [hDt]; exact hc'.2)) X).2.1 ⟨z₀, hz₀⟩]
    have hB' := hSB K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp c hc'.1 (by rw [hDt]; exact hc'.2) X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X ↔ _
    rw [show adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X = {0} from hB',
      Set.mem_singleton_iff, Submodule.Quotient.mk_eq_zero]
    change z₀ ∈ B1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤ ↔ _
    rw [hB, WachMod_mem_B1_iff]
    exact exists_congr fun m => forall_congr' fun g =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).1 g m).symm)
  · intro L₁ z hz
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_rfl, hyp.1⟩
    have hχc : S.Γ.chi 1 = χ 1 := hchi 1 h1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ 1) L₁
    have he' : ∀ g x, e (S.Γ.Wchi 1 g x) = latRep L₁ g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, -, hU⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi 1) (latRep L₁) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep L₁) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 1 h1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1))) (fun x => hcont.mul continuous_const) L₁
    rw [key Tc L₁ z hz', ext_iff 1 (latRep L₁) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi 1) X hkill ((hLc 1 le_rfl (by rw [hDt]; exact hyp.1)) X).2.1 ⟨z₀, hz₀⟩]
    have hC' := hSC K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2 X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi 1) X ↔ _
    rw [hC', GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr]
    rw [SetLike.mem_coe, mk_mem_unr_iff, hU]
    exact exists_congr fun m => forall_congr' fun g => forall_congr' fun _ =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).1 g m).symm)

end GlobalTheory.TopDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.Lower

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem evW_E_ne_zero (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) : bk.evW bk.E ≠ 0 := by
  intro h
  have h0 : bk.ev bk.E = 0 := inclW_injective (h.trans (map_zero _).symm)
  have hu := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  have h1 := hτ.1
  rw [h0, zero_mul] at h1
  have h2 := (hu.map (frobW l)).ne_zero
  rw [frobW_inclW, h1, map_zero] at h2
  exact h2 rfl

theorem map_smul' {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

def raise (bk : BK K) {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (k : ℕ) :
    Frame bk (N + k) d ρ where
  T := F.T
  unit := F.unit
  A := bk.E ^ k • F.A
  A' := bk.E ^ k • F.A'
  A_mul := by
    rw [Matrix.smul_mul, Matrix.mul_smul, F.A_mul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  φ := by
    rw [map_smul', Matrix.mul_smul, ← F.φ, smul_smul, ← map_pow, ← map_pow, ← map_mul, ← pow_add, add_comm]
  fix := F.fix
  ε := F.ε
  gal := F.gal

def lower (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {N₀ k d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Frame bk (N₀ + k) d ρ) (A₀ A₀' : Matrix (Fin d) (Fin d) bk.S) (hA : F.A = bk.E ^ k • A₀)
    (hA' : F.A' = bk.E ^ k • A₀') : Frame bk N₀ d ρ where
  T := F.T
  unit := F.unit
  A := A₀
  A' := A₀'
  A_mul := by
    have h := F.A_mul
    rw [hA, hA', Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.E ^ k * bk.E ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ bk.E_ne_zero) (pow_ne_zero _ bk.E_ne_zero)
    apply mul_left_cancel₀ hE
    rw [h2]; ring
  φ := by
    have h := F.φ
    rw [hA, map_smul', Matrix.mul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.evW (bk.E ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (evW_E_ne_zero bk hτ)
    apply mul_left_cancel₀ hE
    rw [← h2, map_pow]; ring
  fix := F.fix
  ε := F.ε
  gal := F.gal

theorem exists_frame_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  intro l _ K bk τ hτ C hC N N₀ d ρ F hF H hH
  rcases le_total N N₀ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨raise bk F k, rfl, rfl⟩
  · obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    obtain ⟨hdA, hdA'⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τ hτ C hC N d ρ F Y hF hY H).2 N₀ h hH
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left] at hdA hdA'
    choose A₀ hA₀ using hdA
    choose A₀' hA₀' using hdA'
    refine ⟨lower bk hτ F (Matrix.of A₀) (Matrix.of A₀') ?_ ?_, rfl, rfl⟩
    · ext i j; simp [hA₀ i j]
    · ext i j; simp [hA₀' i j]

end GlobalTheory.BKLim.Lower
end
end

