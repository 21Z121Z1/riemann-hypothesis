import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import GroundTheory.AutomorphicForms.FourierWhittaker
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

def conjMap (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) : MMap M' where
  toFun v' := star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩)
  map_update_add' v' i x y := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e, e, ← star_add, ← T.map_update_add]
    congr 3
    ext; simp
  map_update_smul' v' i a x := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e]
    have e2 : (⟨c i ((a • x : M'.sm i) : M'.H i), (h i _).1 (a • x).2⟩ : M.sm i) = star a • ⟨c i x, (h i _).1 x.2⟩ := by
      ext; exact (c i).map_smulₛₗ a x
    rw [e2, T.map_update_smul, star_smul, star_star]

theorem conjMap_apply (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (v' : M'.Vec) :
    conjMap M M' c h T v' = star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) := rfl

theorem conjMap_eq_zero (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (hT : conjMap M M' c h T = 0) : T = 0 := by
  refine MultilinearMap.ext fun v => ?_
  have h1 := congrArg (fun U : MMap M' => U fun τ => ⟨(c τ).symm (v τ), (h τ _).2 (by simpa using (v τ).2)⟩) hT
  simp only [conjMap_apply, LinearIsometryEquiv.apply_symm_apply, Subtype.coe_eta, MultilinearMap.zero_apply,
    star_eq_zero] at h1
  exact h1

theorem mult_congr (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {J : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = χ k) {T : MMap M} (hT : T ∈ Mult θ M J χ) : T ∈ Mult θ M J χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k hk g, hT.equiv, hT.cont⟩

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type}
    (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg Sg' : Pl0 → ℂ[X])
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ))
    (hS : ∀ P k, (Sg' P).coeff k = star ((Sg P).coeff k)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · simp only [hPart, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3 ⊢
      intro P hP k hk α hα R hR
      have h4 := sub_eq_zero.1 (h3 P hP k hk α hα R hR)
      refine sub_eq_zero.2 (MultilinearMap.ext fun v' => funext fun g => ?_)
      have h5 : ∑ γ ∈ R, T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ) =
          ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g :=
        congrArg (fun U : MMap M => U (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g) h4
      show ∑ γ ∈ R, star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ)) =
          ((Sg' P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g)
      rw [← star_sum, h5, hS]
      simp
  let j : (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J χ χ' e e' J0 Pl0 ok pl q Sg hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' J0 ok pl q Sg _ hχ he fun P k => by simp) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e J0 ok pl q _ Sg ?_ ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P k
    simp

end GlobalTheory.ConjDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.PairConj

section Generic

variable {S : Type*} [Ring S]

theorem unop_mul_inv (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem unop_inv_mul (σ : S →+* Sᵐᵒᵖ) (y : Sˣ) : (σ ((y⁻¹ : Sˣ) : S)).unop * (σ (y : S)).unop = 1 := by
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem triv_conj (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) :
    ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop =
      (x : S) * b * (σ (x : S)).unop := by
  have h := unop_mul_inv σ y
  calc ((x * y⁻¹ : Sˣ) : S) * ((y : S) * b * (σ (y : S)).unop) * (σ ((x * y⁻¹ : Sˣ) : S)).unop
      = (x : S) * (((y⁻¹ : Sˣ) : S) * y) * b * ((σ (y : S)).unop * (σ ((y⁻¹ : Sˣ) : S)).unop) *
          (σ (x : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h, mul_one, mul_one]

end Generic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

def shU (y : G.Cˣ) : G.Cˣ :=
  ⟨sh G y, sh G ((y⁻¹ : G.Cˣ) : G.C), unop_mul_inv G.star y, unop_inv_mul G.star y⟩

theorem shU_val (y : G.Cˣ) : ((shU G y : G.Cˣ) : G.C) = sh G y := rfl

def conjAlg (y : G.Cˣ) : G.C →ₐ[G.F] G.C where
  toFun a := y * a * ((y⁻¹ : G.Cˣ) : G.C)
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    show (y : G.C) * algebraMap G.F G.C r * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C r
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem conjAlg_injective (y : G.Cˣ) : Function.Injective (conjAlg G y) := by
  intro a b h
  have h' : (y : G.C) * a * ((y⁻¹ : G.Cˣ) : G.C) = y * b * ((y⁻¹ : G.Cˣ) : G.C) := h
  have := congrArg (fun z => ((y⁻¹ : G.Cˣ) : G.C) * z * (y : G.C)) h'
  simpa [mul_assoc] using this

variable {G} in
theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

variable {G} in

theorem triv_conj_unit (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ)
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]
    rfl
  rw [e, triv_conj, hx]

variable {G}

theorem conj_val (β y : G.Cˣ) : ((y * β * shU G y : G.Cˣ) : G.C) = (y : G.C) * β * sh G y := by
  rw [Units.val_mul, Units.val_mul, shU_val]

def conjPair (P : Pair G) (y : G.Cˣ) : Pair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  trivR := by
    obtain ⟨z, hz⟩ := P.trivR
    have h := triv_conj_unit ℝ (P.β : G.C) y z 1 hz
    rw [← conj_val] at h
    exact ⟨_, h⟩

theorem conjPair_β (P : Pair G) (y : G.Cˣ) :
    (((conjPair P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

end GlobalTheory.LKMid.PairConj

open GlobalTheory.LKMid.PairConj in

theorem GlobalTheory.LKMid.Pair.exists_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (y : G.Cˣ),
    ∃ P' : Pair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  intro p _ G P y
  refine ⟨conjPair P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjPair_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjPair_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LinChange

open MvPowerSeries GlobalTheory.FGDepth

section Rules

variable {K : Type} [Field K] {σ : Type}

private theorem mfact_eq_prod_factorial [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : K) = ∏ x, ((α x).factorial : K) := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

theorem mfact_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : K) = mfact α * ((α l : K) + 1) := by
  rw [mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  have hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) =
      ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

theorem derivAt0_add' (P Q : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g := by
  classical
  rw [derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add,
    derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
    derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem derivAt0_smulP (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (b • P) g = b * derivAt0 P g := by
  classical
  rw [derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem derivAt0_smulG (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 P (b • g) = b * derivAt0 P g := by
  unfold derivAt0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

theorem derivAt0_sumG {κ : Type} (s : Finset κ) (P : MvPolynomial σ K) (f : κ → MvPowerSeries σ K) :
    derivAt0 P (∑ i ∈ s, f i) = ∑ i ∈ s, derivAt0 P (f i) := by
  unfold derivAt0
  simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem derivAt0_C' (a : K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.C a) g = a * constantCoeff g := by
  rw [MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero',
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]

theorem derivAt0_mul_X [Fintype σ] (P : MvPolynomial σ K) (l : σ) (g : MvPowerSeries σ K) :
    derivAt0 (P * MvPolynomial.X l) g = derivAt0 P (pderiv K l g) := by
  classical
  have hP : P * MvPolynomial.X l =
      ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl,
      MvPolynomial.monomial_mul, mul_one]
  rw [hP, DepthAdd.derivAt0_sum]
  conv_rhs => unfold derivAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]
  ring

private theorem constantCoeff_subst_of_constantCoeff_zero' {K ι Λ : Type} [Field K] [Finite ι] (A : ι → MvPowerSeries Λ K)
    (hA : ∀ l, constantCoeff (A l) = 0) (Ψ : MvPowerSeries ι K) :
    constantCoeff (subst A Ψ) = constantCoeff Ψ := by
  have hs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  have h := constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)
  rw [subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

private theorem pderiv_sum_smul_X_eq_C {K ι Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (β : Λ → ι → K)
    (lam : Λ) (l : ι) :
    pderiv K lam (∑ lam', β lam' l • (X lam' : MvPowerSeries Λ K)) = C (β lam l) := by
  rw [map_sum, Finset.sum_eq_single lam]
  · rw [Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro b _ hb
    rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end Rules

end GlobalTheory.IsoTriv.LinChange

namespace GlobalTheory.IsoTriv

open MvPowerSeries GlobalTheory.FGDepth GlobalTheory.IsoTriv.LinChange

theorem linSt_holds : LinSt := by
  unfold LinSt
  intro K _ _ ι Λ _ _ β P
  classical
  have hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0 := by
    intro l
    simp [MvPowerSeries.smul_eq_C_mul]
  induction P using MvPolynomial.induction_on
  · rename_i a
    intro Ψ
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C',
      constantCoeff_subst_of_constantCoeff_zero' _ hA0]
  · rename_i p q hp hq
    intro Ψ
    rw [map_add, derivAt0_add', derivAt0_add', hp, hq]
  · rename_i p lam hp
    intro Ψ
    have hterm : ∀ l : ι, MvPolynomial.aeval
        (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
          (MvPolynomial.C (β lam l) * MvPolynomial.X l) =
        β lam l • (MvPolynomial.aeval
          (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
            MvPolynomial.X l) := by
      intro l
      rw [MvPolynomial.smul_eq_C_mul]
      ring
    rw [map_mul]
    simp only [MvPolynomial.aeval_X]
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [DepthAdd.derivAt0_sum, derivAt0_mul_X,
      ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul,
      derivAt0_smulG]

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.JSW

theorem continuous_whit_infGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g h : GA E a,
      Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  intro E _ _ _ a φ hφ g h
  have hc : Continuous φ.1 := hφ.continuous
  have hW : Continuous (GlobalTheory.JSW.whit φ.1) := by
    have : GlobalTheory.JSW.whit φ.1 = GroundTheory.Automorphic.FourierWhittaker.partialCoeff φ.1 0 := by
      funext x
      exact GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hc x
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hc 0
  exact hW.comp ((continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL).mul continuous_const)

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | exact GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferentialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  first | (exact @GlobalTheory.FormsLocus.polys_ker) | (exact GlobalTheory.FormsLocus.polys_ker) | (intros; apply GlobalTheory.FormsLocus.polys_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFieldsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ := by
  first | exact @GlobalTheory.tieIn_of_nonempty_tie | exact GlobalTheory.tieIn_of_nonempty_tie | (intros; apply GlobalTheory.tieIn_of_nonempty_tie <;> assumption)
end

