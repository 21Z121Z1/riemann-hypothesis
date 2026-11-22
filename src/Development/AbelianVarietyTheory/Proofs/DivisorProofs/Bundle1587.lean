import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousFiniteRealPoint
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section
namespace GlobalTheory.AdelicCoordF

open GlobalTheory.AdelicCoord (incF incI incF_sndA incI_fstA pairA_mul_eq_zero_iff_snd pairA_mul_eq_zero_iff_fst)

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secF : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incF F) LinearMap.id

def secI : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incI F) LinearMap.id

theorem secF_finPart (z : AF F ⊗[F] E) :
    secF F E (Formalism.IndefR.DatumF.finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem secI_infPart (z : AF F ⊗[F] E) :
    secI F E (Formalism.IndefR.DatumF.infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E (pairA F 0 1 • z) = Formalism.IndefR.DatumF.finPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E (pairA F 1 0 • z) = Formalism.IndefR.DatumF.infPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, map_zero]
  · intro h; rw [← finPartF_smul, h, map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, map_zero]
  · intro h; rw [← infPartF_smul, h, map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF F) (w : GlobalTheory.ThetaTransform.VA F N) :
    c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔
        GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔
        GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  intro F E _ _ _ _ _ nS nT N e
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI hA : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin nS → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoordF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstAffineLine

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem spMap_section {k : Type} [Field k] (φ : Polynomial k →+* k)
    (hφ : φ.comp (algebraMap k (Polynomial k)) = RingHom.id k) :
    spMap φ ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
  rw [spMap_comp', hφ, spMap_id']

theorem eq_of_const_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  intro k _ _ Y q _ _ f hq hc a b
  have h1 : (Polynomial.evalRingHom (1 : k)).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext x; simp
  have hs1 := spMap_section _ h1
  set f' := spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom (1 : k)) ≫ f with hf'
  have hlft : LocallyOfFiniteType (f ≫ q) := by
    rw [hq]; exact HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have key : f = f' := by
    refine ext_of_apply_eq (K := k) q
      ((PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))))
      (PrimeSpectrum.basicOpen _).isOpen.isLocallyClosed ?_ ?_ ?_
    · refine IsOpen.dense (X := PrimeSpectrum (Polynomial k)) (PrimeSpectrum.basicOpen _).isOpen
        ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      simp [PrimeSpectrum.mem_basicOpen, Polynomial.X_ne_zero]
    · intro x hx hcl
      have hp := pointOfClosedPoint_comp (f ≫ q) x hcl
      have hpx := pointOfClosedPoint_apply (f ≫ q) x hcl (IsLocalRing.closedPoint k)
      generalize pointOfClosedPoint (f ≫ q) x hcl = p at hp hpx
      rw [hq] at hp
      obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = p := ⟨Spec.preimage p, Spec.map_preimage p⟩
      have hφ : φ.hom.comp (algebraMap k (Polynomial k)) = RingHom.id k := by
        have := Spec.map_injective (show Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ φ)
          = Spec.map (𝟙 _) by rw [Spec.map_comp, Spec.map_id]; exact hp)
        simpa using congrArg CommRingCat.Hom.hom this
      have hev : φ = CommRingCat.ofHom (Polynomial.evalRingHom (φ.hom Polynomial.X)) := by
        apply CommRingCat.hom_ext
        apply Polynomial.ringHom_ext
        · intro a
          rw [Polynomial.algebraMap_eq] at hφ
          simpa using RingHom.congr_fun hφ a
        · simp
      have hc0 : φ.hom Polynomial.X ≠ 0 := by
        intro h0
        rw [← hpx] at hx
        apply (PrimeSpectrum.mem_basicOpen _ _).1 hx
        show φ.hom Polynomial.X ∈ IsLocalRing.maximalIdeal k
        rw [h0]; exact zero_mem _
      have e : Spec.map φ ≫ f = Spec.map φ ≫ f' := by
        rw [hf', reassoc_of% hp, hev]
        exact hc _ hc0
      rw [← hpx]
      exact congrArg (fun g : Sp k ⟶ Y => g (IsLocalRing.closedPoint k)) e
    · rw [hf', Category.assoc, Category.assoc, hq, hs1, Category.comp_id]
  have ha : ∀ a : Polynomial k →ₐ[k] k,
      spMap a.toRingHom ≫ f = spMap (Polynomial.evalRingHom (1 : k)) ≫ f := by
    intro a
    have hsa : spMap a.toRingHom ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ :=
      spMap_section _ (by
        ext x; have := a.commutes x; rw [Polynomial.algebraMap_eq] at this; simpa using this)
    conv_lhs => rw [key]
    rw [hf', reassoc_of% hsa]
  rw [ha a, ha b]

end GlobalTheory.ConstAffineLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngleFormFrameIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ComplexConjugate

noncomputable section
namespace GlobalTheory.CurveDens.FrameIndep

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ : ℂ)) ^ 2 = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem dR_conj {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => conj (f x)) z := by
  simpa using hf.star

theorem dR_ofReal {a : E → ℝ} {z : E} (ha : DifferentiableAt ℝ a z) :
    DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
  (Complex.ofRealCLM.differentiableAt.comp z ha : _)

theorem dR_normSq {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => ‖f x‖ ^ 2) z :=
  hf.norm_sq ℝ

theorem del_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    del (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * del (fun x => (t x : ℂ)) z ξ := by
  rw [del_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem dbar_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    dbar (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * dbar (fun x => (t x : ℂ)) z ξ := by
  rw [dbar_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem ofReal_congr {b c : E → ℝ} {g : E → ℂ} {z : E} (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) :
    (fun x => (b x : ℂ)) =ᶠ[𝓝 z] fun x => g x * conj (g x) * (c x : ℂ) := by
  filter_upwards [e] with x hx
  rw [hx]; push_cast; rw [ofReal_norm_sq]

theorem del_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    del (fun x => (Real.log (b x) : ℂ)) z ξ =
      del (fun x => (Real.log (c x) : ℂ)) z ξ + del g z ξ / g z := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [del_log hbD hb0, del_log hc h0, del_congr (ofReal_congr e),
    del_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), del_mul hgR (dR_conj hgR), del_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero]
  field_simp
  ring

theorem dbar_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    dbar (fun x => (Real.log (b x) : ℂ)) z ξ =
      dbar (fun x => (Real.log (c x) : ℂ)) z ξ + conj (del g z ξ / g z) := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [dbar_log hbD hb0, dbar_log hc h0, dbar_congr (ofReal_congr e),
    dbar_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), dbar_mul hgR (dR_conj hgR), dbar_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero, map_div₀]
  field_simp
  ring

theorem del_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    del (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * del q z ξ + del g z ξ * conj (f z) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar f z ξ = 0 := by rw [dbar_eq_zero hf]; rfl
  rw [del_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    del_mul hgR (dR_conj hfR), del_conj, hz, map_zero]
  ring

theorem dbar_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    dbar (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * dbar q z ξ + g z * conj (del f z ξ) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  rw [dbar_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    dbar_mul hgR (dR_conj hfR), dbar_conj, hz]
  ring

end GlobalTheory.CurveDens.FrameIndep

open GlobalTheory.CurveDens.FrameIndep in

theorem GlobalTheory.CurveDens.angleForm_frame_indep (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' a₂ a₂' : E → ℝ) (q q₂ f g : E → ℂ)
    (ξ z : E) (ha : DifferentiableAt ℝ a z) (ha' : DifferentiableAt ℝ a' z)
    (hq : DifferentiableAt ℝ q z) (ha0 : 0 < a z) (ha0' : 0 < a' z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0)
    (e₂ : a₂ =ᶠ[𝓝 z] fun x => ‖f x‖ ^ 2 * a x) (e₂' : a₂' =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * a' x)
    (eq : q₂ =ᶠ[𝓝 z] fun x => g x * starRingEnd ℂ (f x) * q x) :
    angleForm n a₂ a₂' q₂ ξ z = angleForm n a a' q ξ z := by
  have hqz : q₂ z = g z * conj (f z) * q z := eq.eq_of_nhds
  have haz : a₂ z = ‖f z‖ ^ 2 * a z := e₂.eq_of_nhds
  have haz' : a₂' z = ‖g z‖ ^ 2 * a' z := e₂'.eq_of_nhds
  have hF : ‖f z‖ ≠ 0 := norm_ne_zero_iff.2 hf0
  have hG : ‖g z‖ ≠ 0 := norm_ne_zero_iff.2 hg0
  have hv : ‖q₂ z‖ ^ 2 / (a₂ z * a₂' z) = ‖q z‖ ^ 2 / (a z * a' z) := by
    rw [hqz, haz, haz', norm_mul, norm_mul, Complex.norm_conj]
    field_simp
  unfold angleForm
  rw [hv]
  generalize (((‖q z‖ ^ 2 / (a z * a' z)) ^ n : ℝ) : ℂ) = V
  rw [del_congr eq, dbar_congr eq, del_prod hq hf hg, dbar_prod hq hf hg,
    del_scaled ha' ha0' hg hg0 e₂', dbar_scaled ha ha0 hf hf0 e₂, hqz, haz, haz']
  push_cast
  rw [ofReal_norm_sq, ofReal_norm_sq]
  have h1 : conj (f z) ≠ 0 := (map_ne_zero _).2 hf0
  have h2 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h3 : (a z : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h4 : (a' z : ℂ) ≠ 0 := by exact_mod_cast ha0'.ne'
  simp only [map_mul, map_sub, map_add, map_div₀, map_inv₀, Complex.conj_conj]
  generalize del (fun x => (Real.log (a' x) : ℂ)) z ξ = A
  generalize dbar (fun x => (Real.log (a x) : ℂ)) z ξ = B
  generalize del q z ξ = Q1
  generalize dbar q z ξ = Q2
  generalize del f z ξ = F1
  generalize del g z ξ = G1
  field_simp
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.PsiInfLinear

theorem continuous_ringEquiv_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem psiInf_eq_exp_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F,
      psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  intro D ψ h
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
    refine continuous_const.mul (continuous_finset_sum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (continuous_ringEquiv_mixedSpace_symm D.host.F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [e.symm_apply_apply]

end GlobalTheory.PsiInfLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothing
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SelfSmoothing

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smoothings (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∃ β, IsTest (invSet E a) β ∧ smoothing ν β φ.1 = f}
  zero_mem' := ⟨0, isTest_zero, funext fun x => by simp [smoothing]⟩
  add_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
    refine ⟨β + γ, hβ.add hγ, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_add (hβ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hγ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn))
    simp only [smoothing, Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c _ ⟨β, hβ, rfl⟩
    refine ⟨fun y => β y * c, hβ.mul contDiff_const, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_const_mul c _)
    simp only [smoothing]
    congr 1
    funext y
    ring

theorem exists_smoothing_eq_self : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  intro hP E _ _ _ a ν _ φ hφ
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, -, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V₀ : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  let V' : Submodule ℂ (GA E a → ℂ) := smoothings ν φ ⊓ V₀
  have hf : FiniteDimensional ℂ V' := Submodule.finiteDimensional_of_le (S₂ := V₀) inf_le_right
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨⟨α n, (hα n).1, rfl⟩, ⟨_, hv, rfl⟩⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  exact hφ'.1

end GlobalTheory.AutGrowth.SelfSmoothing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexLineBundleTermTorsionFreeCharZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) → ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 → ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  first | exact @GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | exact GlobalTheory.CechPic.cechLB_X_noZSMulDivisors | (intros; apply GlobalTheory.CechPic.cechLB_X_noZSMulDivisors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassGradedTensorBundleFinsetSumStatement
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ), GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) := by
  first | exact @GlobalTheory.FlagPlucker.cls_LL_sum | exact GlobalTheory.FlagPlucker.cls_LL_sum | (intros; apply GlobalTheory.FlagPlucker.cls_LL_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementCommutesTranslatesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_commutes_translates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), (∀ X, D X * u = u * D X) → ∀ (a : GAd σ J) (f f' : SmG σ J),
      (f'.1 = fun x => f.1 (x * a)) → (u f').1 = fun x => (u f).1 (x * a) := by
  first | exact @GlobalTheory.LeviHC.RightTr.comm_rtr | exact GlobalTheory.LeviHC.RightTr.comm_rtr | (intros; apply GlobalTheory.LeviHC.RightTr.comm_rtr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGraphCoordinatesOpNormLeOfSmallStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartGraphCoordinates_opNorm_le_of_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)),
    (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  first | exact @GlobalTheory.ChartGraph.zN_graphCoord_le | exact GlobalTheory.ChartGraph.zN_graphCoord_le | (intros; apply GlobalTheory.ChartGraph.zN_graphCoord_le <;> assumption)
end

