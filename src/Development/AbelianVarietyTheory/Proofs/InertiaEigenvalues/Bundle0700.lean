import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem hasSupport_of_isSubquotient_prinSeries :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  intro k _ _ _ _ _ n χ hχ π h

  have hd : ∑ a : Fin n, (IrrGL.ofChar (χ a) (hχ a)).1 = n := by
    simp [IrrGL.ofChar]
  refine hasSupport_of_isSubquotient π.irr (fun a => IrrGL.isCusp_ofChar (χ a) (hχ a)) (hd := hd) ?_
  refine h.trans ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ).trans ?_)

  have he : stdBlocks (fun a => (IrrGL.ofChar (χ a) (hχ a)).1) hd =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
    ext ⟨a, i⟩
    rw [stdBlocks_val]
    simp [IrrGL.ofChar, Fin.fin_one_eq_zero i]
    rfl
  unfold prodIrr
  rw [he]

  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin n) (fun _ => Fin 1))
    (fun a => equivRep (IrrRep.det (Fin 1) (χ a) (hχ a)))
  exact IsSubquotient.of_injective φ.toIntertwiningMap (fun u v huv => φ.toLinearEquiv.injective huv)

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportTermSubset
section
noncomputable section

open Formalism.IndefR

namespace GlobalTheory.LawTrace

variable {G Γ W : Type} [Group G] [Group Γ] [AddCommGroup W] [Module ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

open Classical in

def term (y x : G) (P : W) (γ : Γ) : W :=
  if h : (ι γ * y)⁻¹ * x ∈ J then ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • ρ γ P else 0

def tr (y : G) (P : W) : G → W := fun x => ∑ᶠ γ, term ι ρ J χ y x P γ

variable {ι ρ J χ}

theorem support_term_subset (y x : G) (P : W) :
    Function.support (term ι ρ J χ y x P) ⊆ {γ | (ι γ * y)⁻¹ * x ∈ J} := by
  intro γ hγ
  by_contra h
  exact hγ (by unfold term; exact dif_neg (show ¬ ((ι γ * y)⁻¹ * x ∈ J) from h))

theorem finite_cond {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) : {γ | (ι γ * y)⁻¹ * x ∈ J}.Finite := by
  rcases Set.eq_empty_or_nonempty {γ | (ι γ * y)⁻¹ * x ∈ J} with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
    refine (hs.image fun s => γ₀ * s).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
    change γ₀⁻¹ * γ ∈ Bridge.stab ι J y
    rw [Bridge.mem_stab]
    have h1 := J.mul_mem h₀ (J.inv_mem (show (ι γ * y)⁻¹ * x ∈ J from hγ))
    convert h1 using 1
    simp [mul_assoc]

theorem support_term_finite {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) (P : W) :
    (Function.support (term ι ρ J χ y x P)).Finite :=
  (finite_cond hf x).subset (support_term_subset y x P)

theorem term_mul (y x : G) (P : W) (γ₀ γ : Γ) (k : J) :
    term ι ρ J χ y (ι γ₀ * x * k) P (γ₀ * γ) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (term ι ρ J χ y x P γ) := by
  have e : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) = (ι γ * y)⁻¹ * x * k := by
    simp [mul_assoc]
  unfold term
  by_cases h : (ι γ * y)⁻¹ * x ∈ J
  · have h' : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
    rw [dif_pos h', dif_pos h]
    have ek : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
    rw [ek, map_mul, map_mul, Units.val_mul, map_smul, smul_smul, mul_comm, Module.End.mul_apply]
  · have h' : ¬ (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by
      rw [e]; intro h2; exact h (by simpa using J.mul_mem h2 (J.inv_mem k.2))
    rw [dif_neg h', dif_neg h, map_zero, smul_zero]

theorem tr_law {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (γ₀ : Γ) (x : G) (k : J) :
    tr ι ρ J χ y P (ι γ₀ * x * k) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (tr ι ρ J χ y P x) := by
  unfold tr
  rw [← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  simp only [Equiv.coe_mulLeft, term_mul]
  let L : W →ₗ[ℂ] W := ((χ k : ℂˣ) : ℂ) • ρ γ₀
  change ∑ᶠ γ, L (term ι ρ J χ y x P γ) = L (∑ᶠ γ, term ι ρ J χ y x P γ)
  exact (map_finsum L (support_term_finite hf x P)).symm

theorem mem_lawForms_tr {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) :
    tr ι ρ J χ y P ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ :=
  GlobalTheory.ExportSeries.mem_lawForms.2 fun γ x k => tr_law hf P γ x k

theorem tr_add {y : G} (hf : Finite (Bridge.stab ι J y)) (P Q : W) :
    tr ι ρ J χ y (P + Q) = tr ι ρ J χ y P + tr ι ρ J χ y Q := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (P + Q) γ = term ι ρ J χ y x P γ + term ι ρ J χ y x Q γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_add]
  simp only [tr, Pi.add_apply, e]
  exact finsum_add_distrib (support_term_finite hf x P) (support_term_finite hf x Q)

theorem tr_smul (y : G) (a : ℂ) (P : W) : tr ι ρ J χ y (a • P) = a • tr ι ρ J χ y P := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (a • P) γ = a • term ι ρ J χ y x P γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_comm a]
  simp only [tr, Pi.smul_apply, e]
  exact (smul_finsum a _).symm

theorem tr_zero (y : G) : tr ι ρ J χ y (0 : W) = 0 := by
  simpa using tr_smul (ι := ι) (ρ := ρ) (χ := χ) y (0 : ℂ) (0 : W)

theorem tr_mem {R : Type} [Semiring R] [Module R W] {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (x : G)
    (M : Submodule R W) (hM : ∀ γ, (ι γ * y)⁻¹ * x ∈ J → term ι ρ J χ y x P γ ∈ M) : tr ι ρ J χ y P x ∈ M := by
  unfold tr
  rw [finsum_eq_sum _ (support_term_finite hf x P)]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h := support_term_subset y x P ((Set.Finite.mem_toFinset _).1 hγ)
  exact hM γ h

theorem tr_self {y : G} (hf : Finite (Bridge.stab ι J y)) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    tr ι ρ J χ y (F y) y = (Nat.card (Bridge.stab ι J y) : ℂ) • F y := by
  classical
  have e : ∀ γ, term ι ρ J χ y y (F y) γ = if γ ∈ Bridge.stab ι J y then F y else 0 := fun γ => by
    unfold term
    have hc : (ι γ * y)⁻¹ * y ∈ J ↔ γ ∈ Bridge.stab ι J y := by
      rw [Bridge.mem_stab, ← J.inv_mem_iff]
      simp [mul_assoc]
    by_cases h : (ι γ * y)⁻¹ * y ∈ J
    · rw [dif_pos h, if_pos (hc.1 h)]
      have := GlobalTheory.ExportSeries.mem_lawForms.1 hF γ y ⟨_, h⟩
      rw [show ι γ * y * ((ι γ * y)⁻¹ * y) = y by group] at this
      exact this.symm
    · rw [dif_neg h, if_neg fun h' => h (hc.2 h')]
  unfold tr
  simp only [e]
  have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
  have ei : (fun γ => if γ ∈ Bridge.stab ι J y then F y else 0) =
      Set.indicator ((Bridge.stab ι J y : Subgroup Γ) : Set Γ) (fun _ => F y) := by
    funext γ; simp [Set.indicator]
  rw [ei, ← finsum_mem_def]
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset hs]
  rfl

theorem eq_sum_tr {I : Type} [Fintype I] {y : I → G} (hr : Bridge.IsReps ι J y)
    (hf : ∀ i, Finite (Bridge.stab ι J (y i))) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    F = ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ • tr ι ρ J χ (y i) (F (y i)) := by
  funext x
  obtain ⟨i₀, ⟨γ₀, k₀, hx⟩, huniq⟩ := hr x
  rw [Finset.sum_apply, Finset.sum_eq_single i₀]
  · have hne : ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)) ≠ 0 := by
      haveI := hf i₀
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Pi.smul_apply, hx, tr_law (hf i₀), tr_self (hf i₀) hF, GlobalTheory.ExportSeries.mem_lawForms.1 hF γ₀ (y i₀) k₀, map_smul,
      smul_comm ((χ k₀ : ℂˣ) : ℂ) ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)), smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro i _ hi
    rw [Pi.smul_apply]
    have : tr ι ρ J χ (y i) (F (y i)) x = 0 := by
      unfold tr
      refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
      unfold term
      rw [dif_neg]
      intro h
      exact hi (huniq i ⟨γ, ⟨_, h⟩, by simp [mul_assoc]⟩)
    rw [this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LawTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTBRecords

theorem aux_of_blochKato_tateDuality_eulerChar :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        LocalSituation.Conclusion4 D HW F := by
  intro hBK hTD hEC D HW F _Cm
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler hTD hEC D HW F
  exact GlobalTheory.T.twistedTorsionClassTheorem_goodCase D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D)

end GlobalTheory.TheoremTBRecords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pairing_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  first | exact @GlobalTheory.WeilPairing.thetaInner_weilRep | exact GlobalTheory.WeilPairing.thetaInner_weilRep | (intros; apply GlobalTheory.WeilPairing.thetaInner_weilRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

def DCRep {Γ : Type} [Group Γ] (c : Γ →* Γ) (K : Subgroup Γ) (α : Γ) (C : Finset Γ) : Prop :=
  (∀ δ ∈ C, c δ = δ ∧ ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ δ = k₁ * α * k₂) ∧
  ∀ x, (∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ x = k₁ * α * k₂) →
    ∃! δ, δ ∈ C ∧ δ⁻¹ * x ∈ K ∧ c (δ⁻¹ * x) = δ⁻¹ * x

variable {D : D7}

def cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GfC V →* GfC V where
  toFun g := ⟨GlobalTheory.LevelProduct.cmp V v g, GlobalTheory.LevelProduct.cmp_mem_GfC V v g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem cf_val (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    (cf V v g : GA D V) = GlobalTheory.LevelProduct.cmp V v g := rfl

theorem isFinIdem_fE (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (GlobalTheory.LevelProduct.fE D v) :=
  ⟨_, GlobalTheory.LevelProduct.epsF_spec v, rfl⟩

theorem cf_supp (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    SuppF V (GlobalTheory.LevelProduct.fE D v) (cf V v g : GA D V) := GlobalTheory.LevelProduct.cmp_supp V v g

theorem cmp_eq_self {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V}
    (h : SuppF V (GlobalTheory.LevelProduct.fE D v) g) : GlobalTheory.LevelProduct.cmp V v g = g := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, ← (GlobalTheory.IdemSupport.suppF_iff V _ g).1 h, GlobalTheory.IdemSupport.mix_self]

theorem cf_eq_self_iff (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    cf V v g = g ↔ SuppF V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) :=
  ⟨fun h => h ▸ cf_supp V v g, fun h => Subtype.ext (cmp_eq_self h)⟩

theorem trivAt_of_cf_eq_one (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) (h : cf V v g = 1) :
    TrivAt V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) := by
  have e : GlobalTheory.LevelProduct.cmp V v (g : GA D V) = 1 := congrArg Subtype.val h
  have := GlobalTheory.LevelProduct.cmp_triv V v (g : GA D V)
  rwa [e, inv_one, mul_one] at this

theorem cf_cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) : cf V v (cf V v g) = cf V v g :=
  (cf_eq_self_iff V v _).2 (cf_supp V v g)

theorem cf_orth (V : HSp D) {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) (g : GfC V) :
    cf V w (cf V v g) = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ho : GlobalTheory.LevelProduct.fE D w * GlobalTheory.LevelProduct.fE D v = 0 :=
    GlobalTheory.IdemSupport.place_orth hΦ (GlobalTheory.LevelProduct.epsF_spec w) (GlobalTheory.LevelProduct.epsF_spec v) (Ne.symm hvw)
  set h := cf V v g with hh
  have hs := cf_supp V v g
  have ht : TrivAt V (GlobalTheory.LevelProduct.fE D w) (h : GA D V) := by
    intro a b
    rw [← hs a b, ← mul_assoc, ho, zero_mul]
  apply Subtype.ext
  show GlobalTheory.LevelProduct.cmp V w (h : GA D V) = 1
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, GlobalTheory.IdemSupport.mt_one]
  have e : GlobalTheory.LevelProduct.fE D w • mt V (h : GA D V) =
      GlobalTheory.LevelProduct.fE D w • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext a b
    have := ht a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at this
    exact this
  rw [e, GlobalTheory.IdemSupport.mix_self]

abbrev KR {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Subgroup (GfC (Wc D i)) :=
  (levW R i).subgroupOf (GfC (Wc D i))

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem kr_mem_iff (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    g ∈ KR R i ↔ ∀ v, cf (Wc D i) v g ∈ KR R i := by
  have hH : (R.datWp i R.triv).P.H = ⊥ := rfl
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact ⟨fun h v => GlobalTheory.LevelProduct.cmp_mem_of_mem hH h v, fun h => GlobalTheory.LevelProduct.mem_of_cmp_mem hH g.2 h⟩

theorem kr_finite (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    {v | cf (Wc D i) v g ∉ KR R i}.Finite := by
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact GlobalTheory.LevelProduct.finite_cmp (g : GA D (Wc D i))

end GlobalTheory.UpInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInv
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem unr_eq_diag_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro E Ω _ _ _ _ _ A w h y hy
  obtain ⟨n, c, rfl⟩ := GlobalTheory.WeilDeligne.Unram.exists_diag hy
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by simp
  refine ⟨fun i => (c (Fin.cast hn i))⁻¹, ?_⟩
  simp only [inv_inv]
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ (finCongr hn), fun σ v => funext fun k => ?_,
    fun v => by simp⟩
  simp [LinearEquiv.funCongrLeft_apply]

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.SpCharpoly

theorem charpoly_blockDiag {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have e : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, e, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_map_diagEnd {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (c : Fin m → ℂ) :
    LinearMap.charpoly (TensorProduct.map f (diagEnd c)) = ∏ i, LinearMap.charpoly (c i • f) := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  have e : LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (Pi.basisFun ℂ (Fin m)) (diagEnd c) =
      Matrix.diagonal c := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct (Pi.basisFun ℂ (Fin m))),
    TensorProduct.toMatrix_map, e]
  have e2 : Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix b b f) (Matrix.diagonal c) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (c i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [e2, charpoly_blockDiag]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end GlobalTheory.WeilDeligne.SpCharpoly

namespace GlobalTheory.WeilDeligne

theorem charPol_lpTw_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp h 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp h l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  refine ⟨?_, fun l σ => ?_⟩
  · rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp h 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp h 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  · induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecialStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp h n)).lpDual = y.lpDual.lpChar (WD.lpSp h n) := by
  first | exact @GlobalTheory.WDDual.lpDual_sum_tw_sp | exact GlobalTheory.WDDual.lpDual_sum_tw_sp | (intros; apply GlobalTheory.WDDual.lpDual_sum_tw_sp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimpleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_semisimple : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | exact GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | (intros; apply GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompatStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_sum_twist_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  first | exact @GlobalTheory.sumList_laws | exact GlobalTheory.sumList_laws | (intros; apply GlobalTheory.sumList_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestrictionStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_group_restriction : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  first | exact @GlobalTheory.WeilRestrict.weil_restrict | exact GlobalTheory.WeilRestrict.weil_restrict | (intros; apply GlobalTheory.WeilRestrict.weil_restrict <;> assumption)
end

