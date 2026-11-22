import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSummandEmbeddingHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add, add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add, mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))

variable (G) in

theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h

variable (G) in

theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)

variable (G) in

theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dif_pos ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_isCoverIt_swap (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q)
    (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H)
    (hI : ∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y')
    (hE : ∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) :
    ∃ B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H, IsCoverIt R₂ R₁ B := by
  let A : R₁.U.H → F.H →L[ℂ] R₂.U.H := fun x => ContinuousLinearMap.adjoint (Tm x)
  have hC : ∀ x φ y, inner ℂ y (A x φ) = inner ℂ (Tm x y) φ := fun x φ y => by
    simp only [A]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hall : ∀ g h φ x, A (R₁.U.π g x) (F.π (g, h) φ) = R₂.U.π h (A x φ) := by
    intro g h φ x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨y, rfl⟩ : ∃ y', R₂.U.π h y' = y := ⟨R₂.U.π h⁻¹ y, by
      change (R₂.U.π h * R₂.U.π h⁻¹) y = y
      rw [← map_mul]; simp⟩
    rw [hC, ← hE, GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (R₂.U.isom h), hC]
    exact GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (F.isom _) _ _
  have he : ∀ h φ x, A x (F.π (1, h) φ) = R₂.U.π h (A x φ) := fun h φ x => by
    simpa using hall 1 h φ x
  have hi : ∀ g φ x, A (R₁.U.π g x) (F.π (g, 1) φ) = A x φ := fun g φ x => by
    simpa using hall g 1 φ x
  let sw : Pol r s p q →ₗ[ℂ] Pol p q r s := (MvPolynomial.rename Prod.swap).toLinearMap
  have hsw : ∀ P, sw P = MvPolynomial.rename Prod.swap P := fun _ => rfl
  let B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P x => A x (F.ι (sw P)))
      (fun P Q x => by simp only [map_add])
      (fun c P x => by simp only [map_smul, RingHom.id_apply])
      (fun P x x' => by simp only [A, map_add, ContinuousLinearMap.add_apply])
      (fun c P x => by simp only [A, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply])
  have hB : ∀ P x, B P x = A x (F.ι (sw P)) := fun _ _ => rfl
  obtain ⟨-, hd1, hd2⟩ := GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F
  have hsym := GlobalTheory.FockSwap.swap_symmetry r s p q
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    refine ⟨‖F.ι (sw P)‖, fun x => ?_⟩
    rw [hB]
    set φ := F.ι (sw P)
    have h := hC x φ (A x φ)
    have h1 : ‖A x φ‖ * ‖A x φ‖ ≤ ‖A x φ‖ * (‖φ‖ * ‖x‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm x (A x φ)) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (A x φ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  · intro P x
    rw [R₂.ι_range, hB]
    have hf := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) (sw P)).2
    unfold KFin at *
    have : (Set.range fun k : T₂.Kset => R₂.U.π k (A x (F.ι (sw P)))) =
        (A x).toLinearMap '' Set.range fun k : T₂.Kset => F.π (1, k) (F.ι (sw P)) := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance
  · intro x hx
    by_contra hcon
    push_neg at hcon
    have hcon' : ∀ P : Pol p q r s, A x (F.ι P) = 0 := fun P => by
      have := hcon (MvPolynomial.rename Prod.swap P)
      rwa [hB, hsw, MvPolynomial.rename_rename, Prod.swap_swap_eq, MvPolynomial.rename_id_apply] at this
    have h0 : ∀ φ, A x φ = 0 := fun φ =>
      congrFun (Continuous.ext_on F.dense (A x).continuous (continuous_const (y := (0 : R₂.U.H)))
        (by rintro _ ⟨P, rfl⟩; exact hcon' P)) φ
    have := R₂.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R₂.U.H)
    have h := hC x (Tm x y) y
    rw [h0, inner_zero_right, eq_comm, inner_self_eq_zero, ← norm_eq_zero, hn, mul_eq_zero,
      norm_eq_zero, norm_eq_zero] at h
    tauto
  · intro Z hZ P x
    have := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd2 Z hZ (sw P))
    have e1 : sw (fockAct1 r s p q Z P) = fockAct2 p q r s Z (sw P) := hsym.1 Z P
    simpa [hB, Function.comp_def, he, e1] using this
  · intro Z hZ P x
    have h1 := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd1 Z hZ (sw P))
    have h2 := h1.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    have e2 : sw (fockAct2 r s p q Z P) = fockAct1 p q r s Z (sw P) := hsym.2.1 Z P
    have h3 : (fun t : ℝ => B P (R₁.U.π (T₁.expt (t • Z)) x)) =
        fun t : ℝ => A x (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) := by
      funext t
      rw [hB, ← hi (T₁.expt (t • Z)) (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) x]
      congr 1
      change _ = (F.π (T₁.expt (t • Z), 1) * F.π (T₁.expt ((-t) • Z), 1)) _
      rw [← map_mul, Prod.mk_mul_mk, ← T₁.expt_add Z hZ, add_neg_cancel, zero_smul, T₁.expt_zero,
        mul_one, Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]
    rw [h3, hB, e2]
    simpa [Function.comp_def] using h2

end GlobalTheory.Chain.RealItLarge

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt Formalism.MainNotions.SchurIrreducible

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isParam_lamM' {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) : IsParam (lamM' t al be ga de) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have mem : ∀ e, e ∈ ga ++ de ++ al ++ be → e ∈ al ++ be ++ ga ++ de := fun e he => by
    simp only [List.mem_append] at he ⊢
    tauto
  have h' : HypA t ga de al be := by
    refine ⟨h1, by omega, h5, h6, h3, h4, ?_, fun e he => h8 e ?_, fun e he => h9 e ?_, fun e he => h10 e (mem e he),
      fun e he => h11 e (mem e he)⟩
    · refine (List.Perm.nodup_iff ?_).1 h7
      rw [List.append_assoc (al ++ be), List.append_assoc (ga ++ de)]
      exact List.perm_append_comm
    · simp only [List.mem_append] at he ⊢
      tauto
    · simp only [List.mem_append] at he ⊢
      tauto
  obtain ⟨-, -, ⟨p1, p2, p3, p4⟩, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be h'
  let σ : Ix (al.length + de.length) (ga.length + be.length + t) → Ix (ga.length + be.length + t) (al.length + de.length) :=
    Sum.swap
  have e : ∀ a, lamM' t al be ga de a = lamA' t ga de al be (σ a) := fun a => by rcases a with a | a <;> rfl
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [e, e] at hab
    exact Sum.swap_leftInverse.injective (p1 hab)
  · rw [e, e]
    refine p2 _ _ ?_
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  · rw [e]; exact p3 _
  · rw [e, e]; exact p4 _ _

theorem exists_locIt_large {X : ProvA} (hX : ChosenSeries X) (h1 : ArchimedeanRallisFirst X) (h2 : ArchimedeanRallisSecond X)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : DataARm t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ de) (ga ++ block t ++ be) aT))
    (hS' : S' τ = dualPar (signed (al ++ be) (ga ++ de) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
  have p2 := isParam_lamM' hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + de.length) (ga.length + be.length + t) _ _ aT
    ⟨by omega, by simp, by simp [block]; omega, p2, hX _ _ _ p2, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + be.length) (ga.length + de.length) _ _ aS
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.2 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.2 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := exists_isCoverIt_swap _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p1).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

end GlobalTheory.Chain.RealItLarge

theorem GlobalTheory.Chain.RealItLarge.itLarge : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  intro D V W S S' M M' θ ψ t aS aT hD hH hθ hP χS χT ω hω hexp f hf
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, GlobalTheory.Chain.RealIt.LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨be, de, hd, e1, e2⟩ := hP τ
    exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ (al := []) (ga := []) hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (hexp τ).1 (hexp τ).2 hf
  exact ⟨It, GlobalTheory.Chain.RealIt.isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBump
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FlatProdValue

variable {D : D7}

theorem mixT_smul' {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (c • f) y = c • d.mixT S ψ μ 𝓕 f y := by
  funext w
  simp only [HypDec.mixT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext ξ; ring

theorem continuous_psiUni' {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hc)
    · exact continuous_const
  exact hψ.comp (ht.comp hu)

theorem flatS_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℝ) (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), g ≠ 0 → β₂ y ≠ 0 → (∀ x', dV.mixS W ψ s.vS.μ s.vS.𝓕 Φ x' = (β₁ x' : ℂ) • g') → (∀ y', dW.mixT V₀ ψ s.vT.μ s.vT.𝓕 g' y' = β₂ y' • g) → Continuous β₁ → β₁ x = 1 → (∀ z, 0 ≤ β₁ z) → (∀ u : UX D ρ, β₁ (x ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re) → HasCompactSupport (fun u : UX D ρ => β₁ (x ⬝ u.1.1)) → flatS dV dW s x y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x y β₁ β₂ g g' Φ hg hβy hS hT hβc hβx hβ0 hpos hcs
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  haveI : (s.vU.ν).IsHaarMeasure := s.vU.unit.1
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hg
  set F : UX D ρ → ℂ := fun u => star (psiUni ψ u.1) * (β₁ (x ⬝ u.1.1) : ℂ) with hF
  have hval : flatS dV dW s x y Φ w = (∫ u, F u ∂s.vU.ν) * (β₂ y * g w) := by
    simp only [flatS, flatAt, flatFun, evalAt, hS, mixT_smul', hT, Pi.smul_apply, smul_eq_mul, hF]
    rw [← integral_mul_const]
    congr 1; funext u; ring
  have hxc : Continuous fun u : UX D ρ => x ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have hβc' : Continuous fun u : UX D ρ => β₁ (x ⬝ u.1.1) := hβc.comp hxc
  have hFc : Continuous F :=
    (continuous_star.comp (continuous_psiUni' hψ.1.1 ρ)).mul (Complex.continuous_ofReal.comp hβc')
  have hFs : HasCompactSupport F := by
    have : HasCompactSupport fun u : UX D ρ => (β₁ (x ⬝ u.1.1) : ℂ) := hcs.comp_left Complex.ofReal_zero
    exact this.mul_left
  have hFi : Integrable F s.vU.ν := hFc.integrable_of_hasCompactSupport hFs
  have hre : ∀ u, (F u).re = (star (psiUni ψ u.1)).re * β₁ (x ⬝ u.1.1) := by
    intro u; simp [hF, Complex.mul_re]
  have hpos' : 0 < ∫ u, (F u).re ∂s.vU.ν := by
    have hrc : Continuous fun u => (F u).re := Complex.continuous_re.comp hFc
    have hrs : HasCompactSupport fun u => (F u).re := hFs.comp_left Complex.zero_re
    refine hrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hrs (x := 1) ?_ ?_
    · intro u
      simp only [Pi.zero_apply, hre]
      by_cases h0 : β₁ (x ⬝ u.1.1) = 0
      · rw [h0, mul_zero]
      · exact mul_nonneg (hpos u h0).le (hβ0 _)
    · have h1 : x ⬝ ((1 : UX D ρ).1.1) = x := by simp
      rw [hre, h1, hβx, mul_one]
      have := hpos 1 (by rw [h1, hβx]; exact one_ne_zero)
      exact this.ne'
  have hI : (∫ u, F u ∂s.vU.ν) ≠ 0 := by
    intro h0
    have e : ∫ u, (F u).re ∂s.vU.ν = (∫ u, F u ∂s.vU.ν).re := integral_re hFi
    rw [h0, Complex.zero_re] at e
    linarith
  intro h0
  have := congrFun h0 w
  rw [hval, Pi.zero_apply] at this
  exact mul_ne_zero hI (mul_ne_zero hβy hw) this

end GlobalTheory.FlatProdValue

end
end

