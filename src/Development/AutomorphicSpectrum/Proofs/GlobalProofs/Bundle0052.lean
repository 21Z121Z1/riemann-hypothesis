import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPower
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBridge.NotPow

open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (atInf)

theorem exists_ext_surj {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (hw : (InfinitePlace.mk φ).IsComplex) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧ (∀ k : L, e (algebraMap L _ k) = φ k) ∧
      Function.Surjective e ∧ ∀ x, ‖e x‖ = ‖x‖ := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_,
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw, fun x => ?_⟩
    · rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
      rfl
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_, fun y => ?_, fun x => ?_⟩
    · rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
        InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_conj _
    · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
        ((starRingEnd ℂ) y)
      exact ⟨x, by rw [RingHom.comp_apply, hx, Complex.conj_conj]⟩
    · rw [RingHom.comp_apply, Complex.norm_conj]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x

theorem exists_norm_one_zpow_ne (m : ℤ) (hm : m ≠ 0) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ m ≠ 1 := by
  refine ⟨Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_int_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hx : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hx, Complex.exp_pi_mul_I]
  norm_num

private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ c : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous c ∧ ∀ k : L, c (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
    rfl
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
      InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_conj _

private theorem denseRange_units_map_infiniteAdeleRing (E : Type) [Field E] [NumberField E] :
    DenseRange (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom) := by
  have hopen : IsOpenMap (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenMap_val (R := (w : InfinitePlace E) → w.Completion)
  have hd := InfiniteAdeleRing.denseRange_algebraMap E
  rw [DenseRange, dense_iff_inter_open]
  rintro V hV ⟨u, hu⟩
  obtain ⟨_, ⟨u', hu', rfl⟩, k, hk⟩ := hd.inter_open_nonempty _ (hopen V hV) ⟨u, u, hu, rfl⟩
  by_cases hk0 : k = 0
  · have h0 : (u' : InfiniteAdeleRing E) = 0 := by rw [← hk, hk0, map_zero]
    have h01 : (0 : InfiniteAdeleRing E) = 1 := by rw [← u'.mul_inv, h0, zero_mul]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨u', hu', 1, Units.ext (Subsingleton.elim _ _)⟩
  · exact ⟨u', hu', Units.mk0 k hk0, Units.ext (by simpa using hk)⟩

theorem comp_eq {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) {n : I → ℤ}
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (z : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    ((χ.1 (infIdele E _ z) : ℂˣ) : ℂ) =
      (e (z : (InfinitePlace.mk (φ i)).Completion) /
        ((‖e (z : (InfinitePlace.mk (φ i)).Completion)‖ : ℝ) : ℂ)) ^ n i := by
  classical
  choose c₀ hc₀ hc₀' using fun j => exists_inclusion_mul_eq_mul_inclusion_of_normal (φ j)
  let c : ∀ j, (InfinitePlace.mk (φ j)).Completion →+* ℂ := Function.update c₀ i e
  have hc : ∀ j, Continuous (c j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [c] using hec
    · simpa [c, hj] using hc₀ j
  have hc' : ∀ j (k : E), c j (algebraMap E _ k) = φ j k := by
    intro j k
    by_cases hj : j = i
    · subst hj
      simpa [c] using he k
    · simpa [c, hj] using hc₀' j k
  let ι0 : InfiniteAdeleRing E →* NumberField.AdeleRing (NumberField.RingOfIntegers E) E :=
    MonoidHom.inl (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E)
  have hι0 : Continuous ι0 := continuous_id.prodMk continuous_const
  obtain ⟨hχc, -⟩ := χ.2
  let Ψ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ((χ.1 (Units.map ι0 u) : ℂˣ) : ℂ)
  let Θ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ∏ j, (c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) /
      ((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j
  have hne : ∀ (j : I) (u : (InfiniteAdeleRing E)ˣ),
      c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) ≠ 0 := by
    intro j u h0
    have h1 := congrArg (fun x : InfiniteAdeleRing E => x (InfinitePlace.mk (φ j))) u.mul_inv
    have h2 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 0 := (map_eq_zero (c j)).1 h0
    change (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) *
      ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 1 at h1
    rw [h2, zero_mul] at h1
    exact zero_ne_one h1
  have hΨ : Continuous Ψ := Units.continuous_val.comp (hχc.comp (Continuous.units_map ι0 hι0))
  have hΘ : Continuous Θ := by
    refine continuous_finsetProd _ fun j _ => ?_
    have hcont : Continuous fun u : (InfiniteAdeleRing E)ˣ =>
        c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) :=
      (hc j).comp ((continuous_apply (InfinitePlace.mk (φ j))).comp Units.continuous_val)
    have hn0 : ∀ u : (InfiniteAdeleRing E)ˣ,
        (((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ≠ 0 :=
      fun u => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne j u))
    exact (hcont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hcont)) hn0).zpow₀ (n j)
      fun u => Or.inl (div_ne_zero (hne j u) (hn0 u))
  have hkey : Ψ = Θ := by
    refine Continuous.ext_on (denseRange_units_map_infiniteAdeleRing E) hΨ hΘ ?_
    rintro _ ⟨k, rfl⟩
    have hdiag : Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) =
        Formalism.L2.Host.infDiag k := by
      apply Units.ext
      simp only [Formalism.L2.Host.infDiag, MonoidHom.coe_finsetProd, Finset.prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, Units.coe_prod, Units.coe_map]
      have hprod : (∏ w, (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w
          (algebraMap E w.Completion (k : E)) : InfiniteAdeleRing E)) = algebraMap E (InfiniteAdeleRing E) (k : E) :=
        Finset.univ_prod_mulSingle (fun w : InfinitePlace E => algebraMap E w.Completion (k : E))
      rw [Finset.prod_congr rfl fun w _ => (show ((infIdele E w (Formalism.L2.Host.atInf w k) : Neutral.B1.Ideles E) :
          NumberField.AdeleRing (NumberField.RingOfIntegers E) E) =
          ι0 (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w (algebraMap E w.Completion (k : E))) from rfl),
]
      exact (congrArg ι0 hprod.symm).trans (map_prod ι0 _ _)
    have hinf := hn k
    simp only [Formalism.L2.Host.HChar.inf, MonoidHom.coe_comp, Function.comp_apply] at hinf
    show ((χ.1 (Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k)) : ℂˣ) : ℂ) = _
    rw [hdiag]
    refine hinf.trans (Finset.prod_congr rfl fun j _ => ?_)
    show _ = (c j (algebraMap E _ (k : E)) / ((‖c j (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n j
    rw [hc' j]
  have hz := congrFun hkey
    (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z)
  have hι : Units.map ι0
      (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z) =
      infIdele E _ z := by
    apply Units.ext
    rfl
  simp only [Ψ, Θ] at hz
  rw [hι] at hz
  rw [hz, Finset.prod_eq_single i]
  · simp [c]
  · intro j _ hj
    have hw : InfinitePlace.mk (φ j) ≠ InfinitePlace.mk (φ i) := fun h => hj (hb.1 h)
    simp only [Units.coe_map, MonoidHom.coe_mulSingle, MonoidHom.mulSingle_apply]
    rw [Pi.mulSingle_eq_of_ne hw]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ideleModule_infIdele {E : Type} [Field E] [NumberField E] (w : InfinitePlace E)
    (z : (w.Completion)ˣ) :
    (ideleModule E (infIdele E w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  show (IdeleGroup.infiniteModule (infIdele E w z) * IdeleGroup.finiteModule (infIdele E w z) : ℝ) = _
  have hinf : IdeleGroup.infiniteModule (infIdele E w z : IdeleGroup E) = ‖(z : w.Completion)‖ ^ w.mult := by
    unfold IdeleGroup.infiniteModule
    rw [Fintype.prod_eq_single w]
    · show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w‖ ^ w.mult = _
      rw [Pi.mulSingle_eq_same]
    · intro w' hw'
      show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w'‖ ^ w'.mult = 1
      rw [Pi.mulSingle_eq_of_ne hw', norm_one, one_pow]
  have hfin : IdeleGroup.finiteModule (infIdele E w z : IdeleGroup E) = 1 := by
    unfold IdeleGroup.finiteModule
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E) v‖ = 1
    simp
  rw [hinf, hfin, mul_one]

theorem not_modulePow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  intro E _ _ _ I _ φ hcm χ hu n hn hex hτex
  obtain ⟨i, hi⟩ := hex
  obtain ⟨τ, hτ⟩ := hτex
  have hb := GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hcm
  have hw : (InfinitePlace.mk (φ i)).IsComplex := IsTotallyComplex.isComplex _
  obtain ⟨e, hec, he, hes, hen⟩ := exists_ext_surj (φ i) hw
  obtain ⟨ζ, hζ1, hζm⟩ := exists_norm_one_zpow_ne (n i) hi
  obtain ⟨y, rfl⟩ := hes ζ
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hy1 : ‖y‖ = 1 := by rw [← hen]; exact hζ1
  have h3 := comp_eq hb χ hn i e hec he (Units.mk0 y hy0)
  have h4 := ideleModule_infIdele (InfinitePlace.mk (φ i)) (Units.mk0 y hy0)
  have h5 := hτ (infIdele E _ (Units.mk0 y hy0))
  rw [GlobalTheory.CompanionTheory.HeckeBridge.coe_toIdele] at h5
  apply hζm
  simp only [Units.val_mk0] at h3 h4
  rw [hζ1, Complex.ofReal_one, div_one] at h3
  rw [← h3]
  refine h5.trans ?_
  rw [h4, hy1, one_pow, Complex.ofReal_one, Complex.one_cpow]

end GlobalTheory.CompanionTheory.HeckeBridge.NotPow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsBasisLieOfOrthogonal
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in

theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  intro n G hG
  obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
  let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := HCSS.lieOf G
      add_mem' := fun {X Y} hX hY => hadd X Y hX hY
      zero_mem' := fun t => by simpa using hG.one_mem
      smul_mem' := fun r X hX => hsmul r X hX }
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
    FiniteDimensional.complexToReal _
  obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
  have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
  have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
    intro i
    obtain ⟨X, hX, hXe⟩ := heW i
    have : vecOf.symm (e i) = X := by
      rw [← hXe]; simp
    rw [this]; exact hX
  have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
    intro X hX
    have h := hexp _ (hmemW X hX)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa using h2
  refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
  · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
      (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
  · intro X hX
    exact ⟨_, hexpM X hX⟩
  · intro k hk
    have hkG : k ∈ G := hk.1
    have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
    let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
    have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
    have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
      have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
      simpa [f] using this)
    refine ⟨_, hO, fun i => ?_⟩
    have h := hexp _ (hfW i)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa [f] using h2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSum
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PeriodicInt

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)}

theorem valued_algebraMap (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_int_le_one (a : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (a : E)) ≤ 1 := by
  rw [valued_algebraMap]
  exact v.valuation_le_one a

theorem valued_le_one_of_mem_valBall {m : ℕ} {x : v.adicCompletion E}
    (h : x ∈ valBall (v.adicCompletion E) (m : ℤ)) : Valued.v x ≤ 1 := by
  refine (mem_valBall_iff_valued.1 h).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem exists_int_close (m : ℕ) {y : v.adicCompletion E} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 E, y - algebraMap E (v.adicCompletion E) (a : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  have hopen : IsOpen {z : v.adicCompletion E | y - z ∈ valBall (v.adicCompletion E) (m : ℤ)} :=
    (isOpen_valBall (m : ℤ)).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (v.denseRange_algebraMap E).exists_mem_open hopen
    ⟨y, by simp [zero_mem]⟩
  have hx' : y - algebraMap E (v.adicCompletion E) x ∈ valBall (v.adicCompletion E) (m : ℤ) := hx
  have h1 : Valued.v (algebraMap E (v.adicCompletion E) x) ≤ 1 := by
    have e : algebraMap E (v.adicCompletion E) x =
        y - (y - algebraMap E (v.adicCompletion E) x) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hy (valued_le_one_of_mem_valBall hx'))
  rw [valued_algebraMap] at h1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer h1
    (Units.mk0 _ (WithZero.exp_ne_zero (a := -(m : ℤ))))
  rw [Units.val_mk0] at ha
  refine ⟨a, ?_⟩
  have e : y - algebraMap E (v.adicCompletion E) (a : E) =
      (y - algebraMap E (v.adicCompletion E) x) +
        algebraMap E (v.adicCompletion E) (x - (a : E)) := by
    rw [map_sub]; ring
  rw [e]
  refine add_mem hx' (mem_valBall_iff_valued.2 ?_)
  rw [valued_algebraMap, Valuation.map_sub_swap]
  exact ha.le

theorem sub_mem_pow_of_close {m : ℕ} {a b : 𝓞 E}
    (h : algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ)) : a - b ∈ v.asIdeal ^ m := by
  have h1 := mem_valBall_iff_valued.1 h
  rw [← map_sub, valued_algebraMap] at h1
  rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := E)]
  simpa using h1

theorem close_of_sub_mem_pow {m : ℕ} {a b : 𝓞 E} (h : a - b ∈ v.asIdeal ^ m) :
    algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  rw [mem_valBall_iff_valued, ← map_sub, valued_algebraMap]
  exact valuation_sub_le h

theorem integral_eq_finsum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  intro E _ _ v m g h0 hp
  classical
  have : Finite (𝓞 E ⧸ v.asIdeal ^ m) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal ^ m)
  let a : (𝓞 E ⧸ v.asIdeal ^ m) → v.adicCompletion E := fun r =>
    algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)
  let S : (𝓞 E ⧸ v.asIdeal ^ m) → Set (v.adicCompletion E) := fun r =>
    (fun y => y + (-a r)) ⁻¹' (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E))
  have memS : ∀ r y, y ∈ S r ↔ y - a r ∈ valBall (v.adicCompletion E) (m : ℤ) := fun r y => by
    simp only [S, Set.mem_preimage, SetLike.mem_coe, sub_eq_add_neg]
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_valBall (m : ℤ)).preimage (continuous_id.add continuous_const)).measurableSet
  have hB : (haarIntegers (v.adicCompletion E)).real
      (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := by
    rw [measureReal_def, haarIntegers_valBall, residueCard_adicCompletion, ENNReal.coe_toReal,
      NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg, zpow_natCast]
    push_cast
    rfl
  have hSμ : ∀ r, (haarIntegers (v.adicCompletion E)).real (S r) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := fun r => by
    rw [← hB, measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (measure_preimage_add_right _ _ _)
  have hfin : ∀ r, haarIntegers (v.adicCompletion E) (S r) ≠ ⊤ := fun r => by
    have : haarIntegers (v.adicCompletion E) (S r) =
        haarIntegers (v.adicCompletion E)
          (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) :=
      measure_preimage_add_right _ _ _
    rw [this, haarIntegers_valBall]
    exact ENNReal.coe_ne_top
  have hdecomp : ∀ y, g y = ∑ r, (S r).indicator (fun _ => g (a r)) y := by
    intro y
    by_cases hy : Valued.v y ≤ 1
    · obtain ⟨b, hb⟩ := exists_int_close (v := v) m hy
      set r : 𝓞 E ⧸ v.asIdeal ^ m := Ideal.Quotient.mk _ b with hr
      have hclose : a r - algebraMap E (v.adicCompletion E) (b : E) ∈
          valBall (v.adicCompletion E) (m : ℤ) :=
        close_of_sub_mem_pow (Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_out]))
      have hyr : y ∈ S r := by
        rw [memS]
        have e : y - a r = (y - algebraMap E (v.adicCompletion E) (b : E)) -
            (a r - algebraMap E (v.adicCompletion E) (b : E)) := by ring
        rw [e]
        exact sub_mem hb hclose
      rw [Finset.sum_eq_single r, Set.indicator_of_mem hyr]
      · have := hp (a r) (y - a r) (mem_valBall_iff_valued.1 ((memS r y).1 hyr))
        rwa [add_sub_cancel] at this
      · intro r' _ hne
        refine Set.indicator_of_notMem (fun hyr' => hne ?_) _
        have h1 := sub_mem ((memS r y).1 hyr) ((memS r' y).1 hyr')
        have e : y - a r - (y - a r') = a r' - a r := by ring
        rw [e] at h1
        have h2 := sub_mem_pow_of_close h1
        have h3 := Ideal.Quotient.eq.2 h2
        simpa [Ideal.Quotient.mk_out] using h3
      · simp
    · rw [h0 y (not_le.1 hy)]
      refine (Finset.sum_eq_zero fun r _ => Set.indicator_of_notMem (fun hyr => hy ?_) _).symm
      have e : y = (y - a r) + a r := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans
        (max_le (valued_le_one_of_mem_valBall ((memS r y).1 hyr)) (valued_int_le_one _))
  have hint : ∀ r, Integrable ((S r).indicator (fun _ => g (a r)))
      (haarIntegers (v.adicCompletion E)) := fun r =>
    (integrable_indicator_iff (hSm r)).2 (integrableOn_const (hfin r))
  calc ∫ y, g y ∂haarIntegers (v.adicCompletion E)
      = ∫ y, ∑ r, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_congr_ae (Filter.Eventually.of_forall hdecomp)
    _ = ∑ r, ∫ y, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_finsetSum _ fun r _ => hint r
    _ = _ := by
        rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_indicator_const _ (hSm r), hSμ r, Complex.real_smul]
        push_cast
        rfl

end GlobalTheory.CompanionTheory.PeriodicInt
end

