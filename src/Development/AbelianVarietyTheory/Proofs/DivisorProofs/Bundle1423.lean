import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
section
noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.GoodIdemTie

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem idemTie_of_tameTie (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) : GlobalTheory.DimPartsCompare.IdemTie D om :=
  hT.idemTie hG.green

theorem coeff_eq_mapDomain (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) :
    D.ntypes.e0.coeff =
      Finsupp.mapDomain GlobalTheory.DimPartsCompare.pull (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.goodIdem (H := D.host) om).coeff := by
  rw [Finsupp.ext_iff, GlobalTheory.DimPartsCompare.pull_bijective.2.forall]
  simp only [Finsupp.mapDomain_apply GlobalTheory.DimPartsCompare.pull_bijective.1]
  exact idemTie_of_tameTie hG D om hT

end GlobalTheory.GoodIdemTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLatticeStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) • b i ∈ S.M S.T := by
  first | exact @GlobalTheory.HSShort.colCoeff_mem | exact GlobalTheory.HSShort.colCoeff_mem | (intros; apply GlobalTheory.HSShort.colCoeff_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchurStatement
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientSpace_endomorphism_scalar_schur : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  first | exact @GlobalTheory.CoefSchur.endo_scalar | exact GlobalTheory.CoefSchur.endo_scalar | (intros; apply GlobalTheory.CoefSchur.endo_scalar <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderivStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  first | exact @GlobalTheory.CCRFock.polEval_pderiv | exact GlobalTheory.CCRFock.polEval_pderiv | (intros; apply GlobalTheory.CCRFock.polEval_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerIffIntegralUnitsOfModel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, ψ (a * y) = M *ᵥ ψ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun ψ
  let φ : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective φ := Algebra.leftMulMatrix_injective b
  have hφ : φ a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hφ]
  exact (isIntegral_algHom_iff φ hinj).symm

theorem cptPart_iff_intUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e he hint n B ψ x γ hmod hsep τ hτ t
  have hcont := (GlobalTheory.ConjAtPlace.main E hE w).1
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    unfold UL; rw [if_neg hw]
    have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
        (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
          (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
    rw [this]
    refine IsClosed.preimage ?_ isClosed_singleton
    unfold cT
    exact (((Units.continuous_val.matrix_map hcont).matrix_transpose).matrix_mul continuous_const).matrix_mul
      Units.continuous_val
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  have key : ∀ s : twCent (MonoidHom.id (UL n w)) γ,
      IsCompact (closure (Subgroup.zpowers (s : UL n w) : Set (UL n w))) ↔ (τ s : B.Aˣ) ∈ intUnits K.O B.A := by
    intro s
    have hinv : ((τ s : B.Aˣ))⁻¹ = ((τ s⁻¹ : B.T) : B.Aˣ) := by rw [map_inv, Subgroup.coe_inv]
    have hI1 : IsIntegral K.O ((τ s : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B ψ _ _ (hτ s), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((τ s : B.Aˣ))⁻¹ : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [hinv, isIntegral_iff_of_mulVec B ψ _ _ (hτ s⁻¹), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat, Subgroup.coe_inv]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl (s : UL n w)]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  let H' : Subgroup (UL n w) := ((intUnits K.O B.A).comap (B.T.subtype.comp τ.toMonoidHom)).map
    (twCent (MonoidHom.id (UL n w)) γ).subtype
  constructor
  · intro ht
    have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro u ⟨hu, hc⟩
      exact ⟨⟨u, hu⟩, (key ⟨u, hu⟩).1 hc, rfl⟩
    obtain ⟨t₀, ht₀, he₀⟩ := hle ht
    have : t₀ = t := Subtype.ext he₀
    subst this
    exact ht₀
  · intro ht
    exact Subgroup.subset_closure ⟨t.2, (key t).2 ht⟩

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_det_sub_one {n : ℕ} (v : Pl F) (t : GL (Fin n) (AE F E))
    (ht : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    At (evFin F v) (((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1) := by
  intro u hu
  have h := ht u hu
  set c := algebraMap (AF F) (AE F E) u with hc
  let I : Ideal (AE F E) := (Submodule.span (AE F E) {c}).annihilator
  have hmem : ∀ x : AE F E, x ∈ I ↔ c * x = 0 := fun x => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
  have hent : ∀ i j, (t : Matrix (Fin n) (Fin n) (AE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ I :=
    fun i j => by
      rw [hmem]
      have := congrFun (congrFun h i) j
      simpa [Matrix.sub_apply, Algebra.smul_def, hc] using this
  have hq : (Ideal.Quotient.mk I).mapMatrix (t : Matrix (Fin n) (Fin n) (AE F E)) =
      (Ideal.Quotient.mk I).mapMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    ext i j
    exact Ideal.Quotient.eq.2 (hent i j)
  have hd := congrArg Matrix.det hq
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at hd
  have := (hmem _).1 (Ideal.Quotient.eq.1 hd)
  rw [Algebra.smul_def, Matrix.GeneralLinearGroup.val_det_apply]
  exact this

theorem compFin_algebraMap (u : Pl F) (a : AF F) :
    compFin F E u (algebraMap (AF F) (AE F E) a) = algebraMap (Fv F u) (Fv F u ⊗[F] E) (evFin F u a) := by
  simp [compFin, Algebra.TensorProduct.algebraMap_apply]

theorem compInf_algebraMap (w : InfinitePlace F) (a : AF F) :
    compInf F E w (algebraMap (AF F) (AE F E) a) = algebraMap w.Completion (w.Completion ⊗[F] E) (evInf F w a) := by
  simp [compInf, Algebra.TensorProduct.algebraMap_apply]

theorem evFin_inFin_self (v : Pl F) (x : Fv F v) : evFin F v (inFin v x) = x :=
  evalV_singleFin_self v x

theorem evFin_inFin_ne {u v : Pl F} (h : u ≠ v) (x : Fv F v) : evFin F u (inFin v x) = 0 :=
  evalV_singleFin_ne h x

theorem evInf_inFin (w : InfinitePlace F) (v : Pl F) (x : Fv F v) : evInf F w (inFin v x) = 0 := by
  show GlobalTheory.AutFunCompare.evW w 0 = 0
  exact map_zero _

theorem at_inFin_one (v : Pl F) : At (evFin F v) (inFin v (1 : Fv F v)) := by
  intro u hu
  rw [smul_eq_mul]
  refine Prod.ext (mul_zero _) (af_ext fun u' => ?_)
  show evalV F u' (u.2 * singleFin v 1) = evalV F u' 0
  rw [map_mul, map_zero]
  by_cases e : u' = v
  · subst e
    exact mul_eq_zero_of_left hu _
  · rw [evalV_singleFin_ne e, mul_zero]

theorem eq_ideleAt {v : Pl F} {z : (AE F E)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1)) :
    z = ideleAt F E v (unitFin F E v z) := by
  set e : AF F := inFin v 1
  have key := hz (1 - e) (by rw [map_sub, map_one, evFin_inFin_self, sub_self])
  rw [Algebra.smul_def] at key
  refine idele_ext (fun w => ?_) (fun u => ?_)
  · rw [unitInf_ideleAt]
    refine Units.ext ?_
    have := congrArg (compInf F E w) key
    rw [map_mul, compInf_algebraMap, map_sub, map_one, evInf_inFin, sub_zero, map_one, one_mul, map_zero, map_sub,
      map_one, sub_eq_zero] at this
    exact this
  · by_cases huv : u = v
    · subst huv
      rw [unitFin_ideleAt_self]
    · rw [unitFin_ideleAt_ne huv]
      refine Units.ext ?_
      have := congrArg (compFin F E u) key
      rw [map_mul, compFin_algebraMap, map_sub, map_one, evFin_inFin_ne huv, sub_zero, map_one, one_mul, map_zero,
        map_sub, map_one, sub_eq_zero] at this
      exact this

section Lat

variable {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)

def piW' : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

theorem piW'_algebraMap (a : AF F) : piW' h (algebraMap (AF F) (AE F E) a) = complMap h (evFin F v a) := by
  rw [piW', RingHom.comp_apply, compFin_algebraMap, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul]
  simp

theorem piW'_inclR (y : E) : piW' h (inclR (F := F) (AF F) y) = algebraMap E _ y := by
  rw [piW', RingHom.comp_apply]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this, toCompl_tmul, map_one, one_mul]

theorem comp_mem_latAt {d : ℕ} (W : Spc F E d) {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    piW' h ∘ z ∈ latAt w W.L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    have e : piW' h ∘ (a • fun i => inclR (F := F) (AF F) (y i)) =
        (⟨complMap h (evFin F v a), complMap_mem h ha⟩ : Formalism.UG.Ov E w) •
          (fun i => algebraMap E (w.adicCompletion E) (y i)) := by
      funext i
      show piW' h (a • inclR (F := F) (AF F) (y i)) = _
      rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  | zero =>
    convert zero_mem (latAt w W.L) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem lift_mem_latAt {d : ℕ} (W : Spc F E d) {y : Fin d → E} (hy : y ∈ W.L) :
    (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v ∧
      piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => algebraMap E (w.adicCompletion E) (y i) := by
  refine ⟨AddSubgroup.subset_closure ⟨_, at_inFin_one v, ?_, y, hy, rfl⟩, ?_⟩
  · rw [evFin_inFin_self]; exact one_mem _
  · funext i
    show piW' h (inFin v (1 : Fv F v) • inclR (F := F) (AF F) (y i)) = _
    rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR, evFin_inFin_self, map_one, one_mul]

theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (g : Matrix (Fin d) (Fin d) (AE F E))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAt w W.L, (piW' h).mapMatrix g *ᵥ z ∈ latAt w W.L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := lift_mem_latAt h W hy
    show (piW' h).mapMatrix g *ᵥ (fun i => algebraMap E (w.adicCompletion E) (y i)) ∈ _
    rw [← h2]
    have e : (piW' h).mapMatrix g *ᵥ (piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) =
        piW' h ∘ (g *ᵥ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) :=
      funext fun i => (RingHom.map_mulVec (piW' h) g _ i).symm
    rw [e]
    exact comp_mem_latAt h W (hg _ h1)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (piW' h).mapMatrix g *ᵥ (c • x) = c • ((piW' h).mapMatrix g *ᵥ x) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem valued_eq_one_of_isUnit {c : Formalism.UG.Ov E w} (hc : IsUnit c) : Valued.v (c : w.adicCompletion E) = 1 := by
  obtain ⟨c', hc'⟩ := hc.exists_right_inv
  have h1 : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
  have h2 : Valued.v (c' : w.adicCompletion E) ≤ 1 := c'.2
  have h3 : Valued.v (c : w.adicCompletion E) * Valued.v (c' : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, hc']; simp
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ Valued.v (c : w.adicCompletion E) := mul_le_of_le_one_right' h2

theorem valued_det_eq_one (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E)
    (t : GL (Fin d) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    Valued.v (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) = 1 := by
  set T : GL (Fin d) (w.adicCompletion E) := Formalism.UG.bc (piW' h) t with hT
  have hT1 : (T : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix (t : Matrix _ _ _) := rfl
  have hT2 : ((T⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (piW' h).mapMatrix ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) := by
    rw [hT, ← map_inv]; rfl
  have hstab : ∀ z, z ∈ latAt w W.L ↔ (T : Matrix _ _ _) *ᵥ z ∈ latAt w W.L := fun z => by
    refine ⟨fun hz => hT1 ▸ mulVec_mem_latAt h W _ (fun z hz => (ht z hz).1) z hz, fun hz => ?_⟩
    have := mulVec_mem_latAt h W _ (fun z hz => (ht z hz).2) _ hz
    rwa [← hT2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt hw hL.fg hL.span_eq_top
  obtain ⟨m, hm⟩ := ((InertChart.isFrameAt_mul ha (one_mem _)).2 T).1 hstab
  have hdet : Matrix.GeneralLinearGroup.det (a⁻¹ * T * a) = Matrix.GeneralLinearGroup.det T := by
    rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det a), ← mul_assoc, mul_inv_cancel, one_mul]
  have e2 : (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) =
      ((Matrix.GeneralLinearGroup.det T : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hT1, RingHom.map_det]
  rw [e2, ← hdet, ← hm, Matrix.GeneralLinearGroup.val_det_apply]
  have e3 : ((Formalism.UG.bc (Formalism.UG.Ov E w).subtype m : GL (Fin d) (w.adicCompletion E)) :
      Matrix (Fin d) (Fin d) (w.adicCompletion E)).det = ((m.val.det : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    show ((Formalism.UG.Ov E w).subtype.mapMatrix m.val).det = _
    rw [← RingHom.map_det]; rfl
  rw [e3]
  exact valued_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m))

end Lat

end GlobalTheory.InertDetChr

theorem GlobalTheory.InertDetChr.alpha_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hvT t ht
  obtain ⟨ht1, ht2⟩ := ht
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  rw [e1, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  have hunr : GlobalTheory.LFun.UnrAt X.α w := hTr.chars.unrα w (by
    show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
    rw [h]; exact_mod_cast hvT)
  have hv1 := GlobalTheory.InertDetChr.valued_det_eq_one h hw G.W hTr.geo.hW.lat t ht2
  set y : (w.adicCompletion E)ˣ :=
    Units.map (toCompl h).toMonoidHom (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) with hy
  have hyv : (y : w.adicCompletion E) =
      GlobalTheory.InertDetChr.piW' h ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)).det) := by
    rw [hy, Units.coe_map, GlobalTheory.InertDetChr.piW', RingHom.comp_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hu : Formalism.L2.Host.IsUnitAt w y := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hyv]; exact hv1
  have hu2 := hunr y hu
  have hu' : ((Circle.toUnits (X.α (GlobalTheory.LFun.locIdele F w y)) : ℂˣ) : ℂ) = 1 := congrArg Units.val hu2
  rw [Circle.toUnits_apply, Units.val_mk0] at hu'
  exact Circle.ext (by simpa using hu')
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_coordinate_ratio_bounded : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  first | exact @GlobalTheory.cone_ratio_bounded | exact GlobalTheory.cone_ratio_bounded | (intros; apply GlobalTheory.cone_ratio_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.ConjSch

open scoped Classical

noncomputable def conjSch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := (Complex.conjLIE.toContinuousLinearEquiv.contDiff).comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => star (f x)) = Complex.conjLIE ∘ f := rfl
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSch_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSch f x = star (f x) := rfl

theorem star_mem_schA {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨conjSch f, fun y => star (g y),
      ⟨hg.1.comp _, hg.2.comp_left (g := star) (star_zero _)⟩, ?_⟩
    funext y
    simp only [pureA, conjSch_apply, star_mul', mul_comm]
  | zero =>
    simp only [Pi.zero_apply, star_zero]
    exact (schA F κ).zero_mem
  | add x y _ _ hx hy =>
    have := (schA F κ).add_mem hx hy
    convert this using 1
    funext z; simp
  | smul c x _ hx =>
    have := (schA F κ).smul_mem (star c) hx
    convert this using 1
    funext z; simp [star_mul', mul_comm]

end GlobalTheory.ConjSch

theorem GlobalTheory.star_mem_schA_main : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ :=
  fun κ _ => GlobalTheory.ConjSch.star_mem_schA κ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZeroStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  first | exact @GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero | exact GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero | (intros; apply GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingRepresentationInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_representation_injective : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V), Function.Injective (envRepAll R) := by
  first | exact @GlobalTheory.CentralOps.envRepAll_injective | exact GlobalTheory.CentralOps.envRepAll_injective | (intros; apply GlobalTheory.CentralOps.envRepAll_injective <;> assumption)
end

