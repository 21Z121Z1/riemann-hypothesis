import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

noncomputable section

namespace GlobalTheory.DblBox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def rIdx (n d : ℕ) : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ Fin (n + n) × Fin d :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))

@[simp] theorem rIdx_inl (p : Fin n × Fin d) : rIdx n d (.inl p) = (finSumFinEquiv (.inl p.1), p.2) := rfl

@[simp] theorem rIdx_inr (p : Fin n × Fin d) : rIdx n d (.inr p) = (finSumFinEquiv (.inr p.1), p.2) := rfl

def upB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inl i))

def loB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inr i))

def reix {R κ κ' : Type} (e : κ ≃ κ') : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e (Equiv.refl R)).symm

theorem reix_apply {R κ κ' : Type} (e : κ ≃ κ') (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e) := rfl

theorem reix_symm {R κ κ' : Type} (e : κ ≃ κ') : (reix (R := R) e).symm = reix e.symm := rfl

def bx (φ₁ φ₂ : Fn F n d) : Fn F (n + n) d := reix (rIdx n d) (boxFun φ₁ φ₂)

def cj (φ : Fn F n d) : Fn F n d := fun x => starRingEnd ℂ (φ x)

def IsBoxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)) : Prop :=
  ∀ u, cb.e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
    Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm)

section Reindex₂

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem reix_mem_schA (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective φ h
  convert this using 2 with y
  rw [reix_apply]
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

theorem reix_mem_schA_iff (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} : reix e φ ∈ schA F κ' ↔ φ ∈ schA F κ :=
  ⟨fun h => by simpa [← reix_symm] using reix_mem_schA e.symm h, reix_mem_schA e⟩

open scoped Classical in
theorem comp_reix_mem_adm (e : κ ≃ κ') {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ (reix e).toLinearMap ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := h (fun z => g (Function.extend e.symm z 0))
    (GlobalTheory.RestrSchA.sb_comp_extend F e.symm.injective hg)
  refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F e.symm.injective), fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hT, LinearMap.comp_apply]
  congr 1
  funext y
  rw [← GlobalTheory.RestrSchA.pureA_extend F e.symm.injective]
  show pureA F f g (y ∘ e) = _
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

omit [Fintype κ] [Fintype κ'] in
theorem thetaSum_reix (e : κ ≃ κ') (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).symm.tsum_eq fun ξ => φ fun i => algebraMap F (AF F) (ξ i)

theorem schr_reix {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (e : κ ≃ κ') (a b : κ → R)
    (φ : (κ → R) → ℂ) : schr ψ (a ∘ e.symm, b ∘ e.symm) (reix e φ) = reix e (schr ψ (a, b) φ) := by
  funext x
  have h1 : x ⬝ᵥ (b ∘ e.symm) = (x ∘ e) ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  have h2 : (a ∘ e.symm) ⬝ᵥ (b ∘ e.symm) = a ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  simp only [schr, reix_apply, h1, h2]
  congr 2
  funext k
  simp

end Reindex₂

theorem bx_mem_schA {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) : bx φ₁ φ₂ ∈ schA F _ :=
  reix_mem_schA _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)

theorem cj_mem_schA {φ : Fn F n d} (h : φ ∈ schA F _) : cj φ ∈ schA F _ := GlobalTheory.ConjSch.conj_mem_schA φ h

theorem thetaSum_bx {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) :
    thetaSum F (bx φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  rw [bx, thetaSum_reix, GlobalTheory.ThetaBox.thetaSum_boxFun F _ _ φ₁ h₁ φ₂ h₂]

theorem exists_boxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (hJ : J₂ = dblGram finSumFinEquiv J)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (hd : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d), IsBoxCo co cb ∧
      ∀ x : Matrix (Fin (n + n)) (Fin d) E, ∃ y z : Fin (n + n) × Fin d → F,
        cb.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  let S : Matrix (Fin (n + n)) (Fin d) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (LinearEquiv.funCongrLeft (AF F) (Fin d → AE F E) finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let G : (Fin (n + n) × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) (rIdx n d)).trans (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  let e := S.trans ((co.e.prodCongr co.e).trans (T.trans (G.symm.prodCongr G.symm)))
  have he : ∀ u, e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm) := fun u => by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
  have hdot : ∀ a b : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      (a ∘ (rIdx n d).symm) ⬝ᵥ (b ∘ (rIdx n d).symm) = a ⬝ᵥ b := fun a b => by
    simp only [dotProduct]; rw [← (rIdx n d).sum_comp]; simp
  refine ⟨⟨e, fun u v => ?_⟩, he, fun x => ?_⟩
  · rw [hJ, GlobalTheory.DefDoubling.incM_dblGram, GlobalTheory.SWAniso.symp_dblGram, he, he, hdot, hdot,
      sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_neg]
    have h1 := co.form (upB u) (upB v)
    have h2 := co.form (loB u) (loB v)
    refine (congrArg₂ (· - ·) h1 h2).trans ?_
    ring
  · obtain ⟨y, z, h1⟩ := hd (upB x)
    obtain ⟨y', z', h2⟩ := hd (loB x)
    refine ⟨Sum.elim y y' ∘ (rIdx n d).symm, Sum.elim z (-z') ∘ (rIdx n d).symm, ?_⟩
    change e (incM F x) = _
    rw [he, show upB (incM F x) = incM F (upB x) from rfl, show loB (incM F x) = incM F (loB x) from rfl, h1, h2]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, map_neg]

theorem IsBoxCo.rho_reix {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d)}
    {cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)} (h : IsBoxCo co cb)
    (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin (n + n)) (Fin d) (AE F E))
    (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) :
    cb.rho ψ u (reix (rIdx n d) φ) = reix (rIdx n d) (schr ψ (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2)) φ) := by
  rw [Darboux.rho, h u, schr_reix]

end GlobalTheory.DblBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
section
noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneEvFun (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (om : Rep σ G.V G.W) (v : Pl F)
    (ev : ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
    (x : UA σ G.V.J) : ℂ :=
  l (ev (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) (locOp v (om (x, 1)) φ)))

end GlobalTheory.ThK.LemF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLattice
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_blockLat : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  intro k k' _ _ _ _ _ _ _ _ j D D₂ _ _ hj cD ϖ ϖ₂ hϖ hϖ₂ e P P₂ hP x
  have hu : valuation k' (j (ϖ : k)) = valuation k' (ϖ₂ : k') := by
    have h1 := isUnif_map hj hϖ
    exact h1.trans hϖ₂.symm
  have hb : ∀ c : D₂, valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k') =
      valuation k' (j (blockUnits ϖ e P (cD c) : kˣ)) := by
    intro c
    by_cases hc : c ∈ P₂
    · have hc' : cD c ∈ P := (hP c).1 hc
      simp only [blockUnits, if_pos hc, if_pos hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
        map_pow, hu]
    · have hc' : cD c ∉ P := fun h => hc ((hP c).2 h)
      simp [blockUnits, hc, hc']
  show (∀ c, valuation k' (j (x (cD c))) ≤ valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k')) ↔
    ∀ d, valuation k (x d) ≤ valuation k ((blockUnits ϖ e P d : kˣ) : k)
  simp only [hb, val_le_iff hj]
  exact ⟨fun h d => by simpa using h (cD.symm d), fun h c => h (cD c)⟩

end GlobalTheory.PureMatch.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  first | exact @GlobalTheory.FrameTransport.finCl_card_le | exact GlobalTheory.FrameTransport.finCl_card_le | (intros; apply GlobalTheory.FrameTransport.finCl_card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLattices
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x
    simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceOfInputsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_trace_of_inputs : GlobalTheory.Published.LabesseWaldspurger → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishing → HyperZero → EllTrace := by
  first | exact @GlobalTheory.EllTraceProof.ellTrace | exact GlobalTheory.EllTraceProof.ellTrace | (intros; apply GlobalTheory.EllTraceProof.ellTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationAutomorphismCommutesSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_automorphism_commutes_schwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e →
    Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) → IsTame F T.symm.toLinearMap := by
  first | exact @GlobalTheory.EvSymmTame.isTame_symm | exact GlobalTheory.EvSymmTame.isTame_symm | (intros; apply GlobalTheory.EvSymmTame.isTame_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
section
noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_compFin_mem_intLoc_adele (z : AE F E) :
    ∀ᶠ v : Pl F in cofinite, compFin F E v z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' using by rw [map_add]; exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := evFin F v a) h (1 : 𝓞 E)) h'
    change evFin F v a ⊗ₜ[F] e ∈ _
    simpa using this

omit [NumberField E] in

theorem compFin_unitAt_self (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  have h : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  rw [map_add, compFin_smul, compFin_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]

theorem eventually_unitAt_mem_unitsAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) : ∀ᶠ v in cofinite, unitAt E v l ∈ unitsAt E v := by
  filter_upwards [eventually_compFin_mem_intLoc_adele (l : AE F E),
    eventually_compFin_mem_intLoc_adele ((l⁻¹ : (AE F E)ˣ) : AE F E)] with v h h'
  refine mem_unitsAt.2 ⟨unitAt_mem v l, ?_, ?_⟩
  · rwa [compFin_unitAt_self]
  · rwa [← map_inv, compFin_unitAt_self]

end GlobalTheory.ThK.ConeEuler

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubledStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  first | exact @GlobalTheory.SquareModel.exists_isGood_model_conj | exact GlobalTheory.SquareModel.exists_isGood_model_conj | (intros; apply GlobalTheory.SquareModel.exists_isGood_model_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfThetaModelCharacter
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar
variable {D : D7}

theorem coe_chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) (x : (AE D)ˣ) :
    ((chi c θ e x : Circle) : ℂ) = (((c.f (finY D x) : ℂˣ) : ℂ) *
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ c.n τ) ^ e := by
  rw [chi, MonoidHom.zpow_apply, Circle.coe_zpow, MonoidHom.mul_apply, Circle.coe_mul, coe_finChar, coe_infChar]

theorem exists_hecke_of_heckeU : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ), (e = 1 ∨ e = -1) →
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ N ∧ HasFinPart χ c e := by
  intro D N c e he
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : Continuous (chi c θ e) := by
    have h : ((chi c θ e : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (finChar c x * infChar θ c.n x) ^ e := by
      funext x; rw [chi, MonoidHom.zpow_apply, MonoidHom.mul_apply]
    rw [h]
    exact ((GlobalTheory.T.continuous_heckeCharacterFinitePart c).mul (continuous_infChar hθ c.n)).zpow e
  have haut : ∀ a : D.host.Eˣ, chi c θ e (Units.map (incA D).toMonoidHom a) = 1 := by
    intro a
    refine Circle.ext ?_
    rw [coe_chi, finY_incA]
    have h1 : ∀ τ, θ τ (infPart D ((Units.map (incA D).toMonoidHom a : (AE D)ˣ) : AE D)) = embT D τ (a : D.host.E) :=
      fun τ => GlobalTheory.FockCompare.comp_incA hθ τ _
    simp only [h1]
    rw [c.aut a, one_zpow, Circle.coe_one]
  refine ⟨chi c θ e, ⟨hcont, haut⟩, ?_, fun x y hxy => ?_⟩
  · refine GlobalTheory.T.heckeChar_restricts_eta_pow_of_sign D _ N ⟨hcont, haut⟩ (fun x y hy => Circle.ext ?_) θ hθ fun τ x h1 h2 h3 => ?_
    · rw [coe_chi, finY_mul_conj x y hy, c.norm, Units.val_one, one_mul, Circle.coe_one]
      have h4 : ∀ τ, θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ) = 1 := by
        intro τ
        have e1 : θ τ (infPart D (y : AE D)) = (Complex.normSq (θ τ (infPart D (x : AE D))) : ℂ) := by
          rw [hy, RingHom.map_mul, map_mul, GlobalTheory.FockCompare.comp_cA hθ, Complex.mul_conj]
        have hne : θ τ (infPart D (x : AE D)) ≠ 0 := by
          intro h0
          have := congrArg (fun z => θ τ (infPart D z)) (Units.mul_inv x)
          simp only [RingHom.map_mul, map_mul, h0, zero_mul, RingHom.map_one, map_one] at this
          exact zero_ne_one this
        have hp : 0 < Complex.normSq (θ τ (infPart D (x : AE D))) := Complex.normSq_pos.2 hne
        rw [e1, Complex.norm_real, Real.norm_of_nonneg hp.le]
        exact div_self (by exact_mod_cast hp.ne')
      simp only [h4, one_zpow, Finset.prod_const_one, one_zpow]
    · have hf : finY D x = 1 := Units.ext (by
        rw [coe_finY, h1, map_one, map_one, Units.val_one])
      rw [coe_chi, hf, map_one, Units.val_one, one_mul, Finset.prod_eq_single τ (fun τ' _ hτ' => by
        rw [h3 τ' hτ']; simp) (fun h => absurd (Finset.mem_univ τ) h), h2]
      have hn : (-1 : ℂ) / (‖(-1 : ℂ)‖ : ℂ) = -1 := by simp
      rw [hn, ← zpow_mul]
      obtain ⟨k, hk⟩ := c.par τ
      have hodd : Odd e := by rcases he with rfl | rfl <;> decide
      obtain ⟨j, hj⟩ := hodd
      have : c.n τ * e = (N : ℤ) + 2 * (k * e + j * (N : ℤ) - (N : ℤ) * 0) := by
        have : c.n τ = k + k + N := by linarith
        rw [this, hj]; ring
      rw [this, zpow_add₀ (by norm_num), zpow_mul, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, mul_one,
        zpow_natCast]
  · obtain ⟨h1, h2⟩ := hxy
    have hy : finY D x = y := Units.ext (by rw [coe_finY, h2, RingEquiv.symm_apply_apply])
    rw [coe_chi, hy, h1]
    simp only [map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one, mul_one]
    rw [Units.val_zpow_eq_zpow_val]

end GlobalTheory.HeckeUChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrameStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  first | exact @GlobalTheory.FrameExt.exists_fr | exact GlobalTheory.FrameExt.exists_fr | (intros; apply GlobalTheory.FrameExt.exists_fr <;> assumption)
end

