import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStagesProof

section Groups

open Matrix

variable {R : Type} [CommRing R]

theorem mem_unipRad_iff_entries' {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [mem_parab.1 hp i j h, one_apply_ne (fun hij' => by rw [hij'] at h; exact lt_irrefl _ h)]
    · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hd _ x y]
      simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
  · intro h
    refine ⟨fun i j hji => ?_, fun a x y => ?_⟩
    · rw [h i j (not_lt.2 hji.le), one_apply_ne (fun hij' => by rw [hij'] at hji; exact lt_irrefl _ hji)]
    · rw [h _ _ (by simp)]
      simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

variable {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem sigma_eq_of_refine (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (a : Fin s) (y : Fin (d a)) :
    ∀ (p : Σ a, Fin (t a)) (i : Fin (d' p.1 p.2)),
      (⟨p.1, e' p.1 ⟨p.2, i⟩⟩ : Σ a, Fin (d a)) = ⟨a, y⟩ → p = ⟨a, blk (e' a) y⟩ := by
  rintro ⟨a', b⟩ i h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq h2
  simp

theorem symm_blk_refinePlace (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (y : Fin (d a)) :
    finSigmaFinEquiv.symm (blk (refinePlace e e') (e ⟨a, y⟩)) = ⟨a, blk (e' a) y⟩ := by
  obtain ⟨⟨c, i⟩, hc⟩ := (refinePlace e e').surjective (e ⟨a, y⟩)
  rw [← hc, blk_apply]
  rw [refinePlace_apply] at hc
  exact sigma_eq_of_refine e' a y _ i (e.injective hc)

theorem blk_eq_fst (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (x : Fin n) :
    blk e x = (finSigmaFinEquiv.symm (blk (refinePlace e e') x)).1 := by
  obtain ⟨⟨a, y⟩, rfl⟩ := e.surjective x
  rw [symm_blk_refinePlace, blk_apply]

theorem blk_refine_lt_iff (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (x y : Fin n) :
    blk (refinePlace e e') x < blk (refinePlace e e') y ↔
      toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') x)) <
        toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') y)) :=
  (GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt.symm

theorem blk_refine_lt_of_lt (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {x y : Fin n} (h : blk e x < blk e y) : blk (refinePlace e e') x < blk (refinePlace e e') y := by
  rw [blk_refine_lt_iff]
  rw [blk_eq_fst e e', blk_eq_fst e e' y] at h
  exact Sigma.Lex.lt_def.2 (Or.inl h)

theorem blk_refine_lt_iff_same (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (x y : Fin (d a)) :
    blk (refinePlace e e') (e ⟨a, x⟩) < blk (refinePlace e e') (e ⟨a, y⟩) ↔ blk (e' a) x < blk (e' a) y := by
  rw [blk_refine_lt_iff, symm_blk_refinePlace, symm_blk_refinePlace, Sigma.Lex.lt_def]
  constructor
  · rintro (h | ⟨h, h2⟩)
    · exact absurd h (lt_irrefl _)
    · exact h2
  · intro h
    exact Or.inr ⟨rfl, h⟩

end Groups

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

section Groups2

open Matrix

variable {R : Type} [Field R] [ValuativeRel R] [TopologicalSpace R] [IsNonarchimedeanLocalField R] {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem one_apply_e (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) (x y : Fin (d a)) :
    (1 : Matrix (Fin n) (Fin n) R) (e ⟨a, x⟩) (e ⟨a, y⟩) = (1 : Matrix (Fin (d a)) (Fin (d a)) R) x y := by
  simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem unipRad_le_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    unipRad R e ≤ unipRad R (refinePlace e e') := by
  intro u hu
  rw [mem_unipRad_iff_entries'] at hu ⊢
  exact fun i j h => hu i j fun h' => h (blk_refine_lt_of_lt e e' h')

theorem leviEmb_mem_unipRad_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (l : ∀ a, GL (Fin (d a)) R) (hl : l ∈ relUnipD R e') :
    leviEmb R e l ∈ unipRad R (refinePlace e e') := by
  rw [mem_unipRad_iff_entries']
  intro i j h
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, one_apply_e]
    have := mem_unipRad_iff_entries'.1 (hl a (Set.mem_univ a)) x y
      (fun h' => h ((blk_refine_lt_iff_same e e' a x y).2 h'))
    exact this
  · rw [leviEmb_apply_ne R e l hab, one_apply_ne]
    intro h'
    exact hab (congrArg Sigma.fst (e.injective h'))

theorem exists_decomp_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (u : GL (Fin n) R) (hu : u ∈ unipRad R (refinePlace e e')) :
    ∃ l ∈ relUnipD R e', ∃ u' ∈ unipRad R e, u = leviEmb R e l * u' := by
  have hu' := mem_unipRad_iff_entries'.1 hu
  have hp : u ∈ parab R e := by
    refine mem_parab.2 fun i j hji => ?_
    have h1 := blk_refine_lt_of_lt e e' hji
    rw [hu' i j (not_lt.2 h1.le), one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hji
  obtain ⟨w, hw, hdec⟩ := exists_levi_mul_unip R e ⟨u, hp⟩
  refine ⟨leviProj R e ⟨u, hp⟩, fun a _ => ?_, w, hw, hdec⟩
  show leviProj R e ⟨u, hp⟩ a ∈ unipRad R (e' a)
  rw [mem_unipRad_iff_entries']
  intro x y h
  rw [leviProj_apply, ← one_apply_e e]
  exact hu' _ _ fun h' => h ((blk_refine_lt_iff_same e e' a x y).1 h')

theorem leviEmb_relEmbD_ne (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    ∀ (p p' : Σ a, Fin (t a)), p ≠ p' → ∀ (x : Fin (d' p.1 p.2)) (y : Fin (d' p'.1 p'.2)),
      (leviEmb R e (relEmbD R e' g) : Matrix (Fin n) (Fin n) R) (e ⟨p.1, e' _ ⟨p.2, x⟩⟩)
        (e ⟨p'.1, e' _ ⟨p'.2, y⟩⟩) = 0 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hne x y
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    rw [leviEmb_apply_same, relEmbD_apply]
    exact leviEmb_apply_ne R (e' a) (g a) hb x y
  · exact leviEmb_apply_ne R e _ ha _ _

theorem leviEmb_refine_flatHom (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    leviEmb R (refinePlace e e') (flatHom (fun a b => GL (Fin (d' a b)) R) g) =
      leviEmb R e (relEmbD R e' g) := by
  ext i j
  obtain ⟨⟨c, x⟩, rfl⟩ := (refinePlace e e').surjective i
  obtain ⟨⟨c', y⟩, rfl⟩ := (refinePlace e e').surjective j
  by_cases hc : c = c'
  · subst hc
    rw [leviEmb_apply_same, refinePlace_apply, refinePlace_apply, leviEmb_apply_same, relEmbD_apply,
      leviEmb_apply_same, flatHom_apply]
  · rw [leviEmb_apply_ne R _ _ hc, refinePlace_apply, refinePlace_apply]
    exact (leviEmb_relEmbD_ne e e' g _ _ (fun h => hc (finSigmaFinEquiv.symm.injective h)) x y).symm

end Groups2

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

theorem deltaHalf_relUnipD {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (l : ∀ a, GL (Fin (d a)) k) (hl : l ∈ relUnipD k e') :
    deltaHalf k (fun a => Fin (d a)) l = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad k (hl a (Set.mem_univ a)), map_one]

theorem jac_refinePlace_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V),
    Nonempty (Representation.Equiv ((jac (refinePlace e e') π).comp (flatHom fun a b => GL (Fin (d' a b)) k))
      (relJacD e' (jac e π))) := by
  intro k _ _ _ _ s n d e t d' e' V _ _ π
  classical
  set A := twKer π (unipRad k e) 1 with hA
  set B := twKer π (unipRad k (refinePlace e e')) 1 with hB
  set C : Submodule ℂ V := Submodule.span ℂ
    {w | ∃ (l : relUnipD k e') (v : V), w = π (leviEmb k e (l : ∀ a, GL (Fin (d a)) k)) v - v} with hC
  have hAB : A ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨u, unipRad_le_refine e e' u.2⟩, v, rfl⟩
  have hCB : C ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, v, rfl⟩
    exact Submodule.subset_span ⟨⟨_, leviEmb_mem_unipRad_refine e e' l.1 l.2⟩, v, by simp⟩
  have hBAC : B ≤ A ⊔ C := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨l, hl, u', hu', hu⟩ := exists_decomp_refine e e' u.1 u.2
    have : π (u : GL (Fin n) k) v - ((1 : unipRad k (refinePlace e e') →* ℂˣ) u : ℂ) • v =
        (π u' v - ((1 : unipRad k e →* ℂˣ) ⟨u', hu'⟩ : ℂ) • v) +
          (π (leviEmb k e l) (π u' v) - π u' v) := by
      rw [hu, map_mul, Module.End.mul_apply]; simp
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨⟨u', hu'⟩, v, rfl⟩)
      (Submodule.subset_span ⟨⟨l, hl⟩, π u' v, rfl⟩)
  have hK : twKer (jac e π) (relUnipD k e') 1 = B.map A.mkQ := by
    have hB' : B.map A.mkQ = C.map A.mkQ := by
      rw [le_antisymm hBAC (sup_le hAB hCB), Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    rw [hB', hC, Submodule.map_span]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨l, x, rfl⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine Submodule.subset_span ⟨_, ⟨l, v, rfl⟩, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨l, v, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨l, Submodule.Quotient.mk v, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
  let φ : (V ⧸ B) ≃ₗ[ℂ] (V ⧸ A) ⧸ twKer (jac e π) (relUnipD k e') 1 :=
    (Submodule.quotientQuotientEquivQuotient A B hAB).symm.trans (Submodule.quotEquivOfEq _ _ hK.symm)
  have hφ : ∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (Submodule.Quotient.mk v) := by
    intro v
    simp only [φ, LinearEquiv.trans_apply]
    rw [show (Submodule.quotientQuotientEquivQuotient A B hAB).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (Submodule.Quotient.mk v) from
        (LinearEquiv.symm_apply_eq _).2 rfl]
    rfl
  refine ⟨Representation.Equiv.mk φ fun g => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [jac_mk, map_smul, hφ, hφ, relJacD_mk, jac_mk, leviEmb_refine_flatHom, GlobalTheory.T.parabolicModulusSqrtChar_refinedBlocks_in_stages k s d t d' e' g, Submodule.Quotient.mk_smul, smul_smul, mul_inv,
    Units.val_mul, mul_comm]

end GlobalTheory.JacStagesProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianStabilizerNormalizesFrameUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  first | exact @GlobalTheory.RallisCusp.conj_mem_NI | exact GlobalTheory.RallisCusp.conj_mem_NI | (intros; apply GlobalTheory.RallisCusp.conj_mem_NI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LangExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (WD.lpSum (h := h)) :=
    ⟨fun a b c => by rw [← WD.lpSum_assoc, WD.lpSum_comm a b, WD.lpSum_assoc]⟩
  exact hp.foldr_eq _

theorem charZero_adicCompletion : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

end GlobalTheory.LocLanglands.LangExt

open GlobalTheory.LocLanglands.LangExt in

theorem GlobalTheory.LocLanglands.exists_isLExt : LanglandsExhaustionGL → LanglandsMultisegments → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (r : IrrGL (w.adicCompletion E) → WD h), (∃ rc, IsLExt r rc) ∧ ∀ rc, IsLExt r rc → ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → rc x = r x := by
  intro hX hM E Ω _ _ _ _ _ A w h r
  haveI : CharZero (w.adicCompletion E) := charZero_adicCompletion
  refine ⟨⟨fun x => segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList, ?_⟩, ?_⟩
  · intro l x hl
    have hm := Classical.choose_spec (hX (w.adicCompletion E) x)
    have he := (hM (w.adicCompletion E)).1 _ _ x hm hl
    show segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList = segSum r l
    unfold segSum
    apply sumList_perm
    apply List.Perm.map
    apply Multiset.coe_eq_coe.1
    rw [Multiset.coe_toList]
    exact he
  · intro rc hrc x hx
    have h1 := hrc [.single x hx] x (single_spec hx).2.2.2
    rw [h1]
    change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h) = r x
    rw [WD.lpSum_zero]
    have h2 := (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r x)).1
    have h3 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
    rw [h3]
    exact h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeStableUnderAction
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

theorem latKeep : ∀ (D : D7) (V W : HSp D) (F : GlobalTheory.ExportSeries.Frame V W), F.Good → ∀ k ∈ GfC V,
    Formalism.UG.bc (Lev.swapAE D) (finPt V k).1 ∈ Formalism.L2.DIV.St F.βS →
    ∀ u : WO V W, u ∈ F.lat ↔ actO V W k 1 u ∈ F.lat := by
  intro D V W F hF k _ hk u
  obtain ⟨y, hy⟩ := hk
  have hfin : ((Formalism.UG.bc (Lev.swapAE D) (finPt V k).1 : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D))
      = (mt V k).map (toEAf D) := rfl
  have hβ' : Formalism.L2.DIV.IsFrame (F.βS * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) F.ΛS := isFrame_mul_intGL hF.frS y
  have hg : (F.βS * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y).val = (mt V k).map (toEAf D) * F.βS.val := by
    rw [← hfin, ← hy]
    simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, Matrix.mul_assoc]
  have hh : F.βT.val = (mt W 1).map (toEAf D) * F.βT.val := by
    have h1 : (mt W 1).map (toEAf D) = 1 := by
      rw [GlobalTheory.AdelicLatMove.mt_one]
      exact Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one
    rw [h1, Matrix.one_mul]
  constructor
  · intro hu
    exact GlobalTheory.AdelicLatMove.actO_mem_latO V W k 1 F.ΛS F.ΛS F.ΛT F.ΛT F.βS _ F.βT F.βT hF.frS hβ' hF.frT hF.frT hg hh u hu
  · intro hu
    have h2 := GlobalTheory.AdelicLatMove.actO_mem_latO V W k⁻¹ 1⁻¹ F.ΛS F.ΛS F.ΛT F.ΛT _ F.βS F.βT F.βT hβ' hF.frS hF.frT hF.frT
      (GlobalTheory.AdelicLatMove.frame_inv V k _ _ hg) (GlobalTheory.AdelicLatMove.frame_inv W 1 _ _ hh) _ hu
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W k⁻¹ 1⁻¹ u
    rw [inv_inv, inv_inv] at e
    rw [e] at h2
    exact h2

end GlobalTheory.LatKeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinUnitOfUniformizer
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeTate

theorem ord_zpow_units {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) (n : ℤ) : GlobalTheory.SmGL.ord k (x ^ n) = n * GlobalTheory.SmGL.ord k x := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord k y)
      map_one' := by rw [GlobalTheory.SmGL.ord_eq_zero (by simp)]; rfl
      map_mul' := fun y z => by rw [GlobalTheory.SmGL.ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f x n)
  simpa [f] using this

theorem isUnit_artin_mul_zpow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (σ : Weil h) (π u : 𝒪[w.adicCompletion E]),
    Irreducible π → (u : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
    IsUnit u := by
  intro E Ω _ _ _ _ _ A w h a ha σ π u hπ hu
  set K := w.adicCompletion E
  have hint := Valuation.integer.integers (valuation K)
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have hπle : valuation K (π : K) ≤ 1 := π.2
  have hπlt : valuation K (π : K) < 1 := by
    have := hπ.not_isUnit
    rw [hint.isUnit_iff_valuation_eq_one] at this
    exact lt_of_le_of_ne hπle this
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer K
  have hπv : valuation K (π : K) = uniformizer K := by
    apply le_antisymm (le_uniformizer_iff.2 hπlt)
    by_contra hlt
    push_neg at hlt
    have hϖ0 : (ϖ : K) ≠ 0 := ϖ.ne_zero
    have hpos : (0 : ValueGroupWithZero K) < valuation K (ϖ : K) := by
      rw [hϖ]; exact zero_lt_iff.2 uniformizer_ne_zero
    have hq : valuation K ((π : K) * (ϖ : K)⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      exact (mul_inv_lt_iff₀ hpos).2 (by rw [one_mul, hϖ]; exact hlt)
    let x : 𝒪[K] := ⟨ϖ, by show valuation K (ϖ : K) ≤ 1; rw [hϖ]; exact uniformizer_lt_one.le⟩
    let y : 𝒪[K] := ⟨(π : K) * (ϖ : K)⁻¹, hq.le⟩
    have hxy : π = x * y := Subtype.ext (by
      show (π : K) = (ϖ : K) * ((π : K) * (ϖ : K)⁻¹)
      field_simp)
    rcases hπ.isUnit_or_isUnit hxy with hx | hy
    · rw [hint.isUnit_iff_valuation_eq_one] at hx
      exact uniformizer_lt_one.ne (hϖ ▸ hx)
    · rw [hint.isUnit_iff_valuation_eq_one] at hy
      exact hq.ne hy
  let p : Kˣ := Units.mk0 _ hπ0
  have hp1 : GlobalTheory.SmGL.ord K p = 1 := GlobalTheory.SmGL.ord_eq_one hπv
  have hd := ha.ord_eq σ
  have hz : GlobalTheory.SmGL.ord K (a σ * p ^ deg σ) = 0 := by
    rw [GlobalTheory.SmGL.ord_mul, ord_zpow_units, hd, hp1]; ring
  have hv := GlobalTheory.SmGL.ord_eq_zero_iff.1 hz
  rw [hint.isUnit_iff_valuation_eq_one]
  show valuation K (u : K) = 1
  rw [hu]
  simpa [p, Units.val_zpow_eq_zpow_val] using hv

end GlobalTheory.HeckeTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  first | exact @GlobalTheory.RawLift.Eu.acoef_small | exact GlobalTheory.RawLift.Eu.acoef_small | (intros; apply GlobalTheory.RawLift.Eu.acoef_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | exact GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | (intros; apply GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar <;> assumption)
end

