import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.Bundle0063
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU E a) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 hx).trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

theorem mem_integral_iff (k : finU E a) :
    k ∈ (AdelicGLn.integralFiniteGL E a).comap (finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
  rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isCompact_integral :
    IsCompact (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a)) := by
  have hO : IsOpen (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a)) :=
    (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.Cong.AutFormFix

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

theorem fixed_intU_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ),
    IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  intro E _ _ _ a φ hφ
  classical
  set St : Set (finU E a) := {k : finU E a | RU E a k φ = φ} with hSt
  set K₀ : Set (finU E a) := (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a))
  let t : Finset (HeightOneSpectrum (𝓞 E)) → Set (finU E a) := fun S =>
    {k : finU E a | ∀ u ∈ S, cLoc u k.1 = 1} ∩ Stᶜ
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    refine IsClosed.inter ?_ hφ.level.isClosed_compl
    have : {k : finU E a | ∀ u ∈ S, cLoc u k.1 = 1} = ⋂ u ∈ S, {k : finU E a | cLoc u k.1 = 1} := by
      ext k; simp
    rw [this]
    refine isClosed_biInter fun u _ => ?_
    haveI : T2Space (GL (Fin a) (u.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
  have hst : K₀ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun k hk => ?_
    have hall : ∀ u, cLoc u k.1 = 1 := fun u =>
      (Set.mem_iInter.1 hk.2 {u}).1 u (Finset.mem_singleton_self u)
    have h1 : k = 1 := Subtype.ext (eq_one_of_forall_cLoc k.2 hall)
    have hnot := (Set.mem_iInter.1 hk.2 ∅).2
    apply hnot
    rw [h1]
    show RU E a ((1 : finU E a) : UA E a) φ = φ
    rw [Subgroup.coe_one, map_one]; rfl
  have hdt : Directed (· ⊇ ·) t := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩ <;> rintro k ⟨hk, hk'⟩ <;> refine ⟨fun u hu => hk u ?_, hk'⟩ <;> simp [hu]
  obtain ⟨S, hS⟩ := isCompact_integral.elim_directed_family_closed t htc hst hdt
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ u ∈ S, Apart u w}.Finite := by
    refine ((S.finite_toSet.biUnion fun u _ => (Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} : Set _)))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq, not_forall, Apart, not_not] at hw
    obtain ⟨u, hu, he⟩ := hw
    refine Set.mem_biUnion hu ?_
    rcases eq_or_eq_conjSrc he.symm with rfl | rfl
    · simp
    · simp
  refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hS'
  apply hw
  intro x hx
  obtain ⟨hxl, hxi⟩ := GlobalTheory.Cong.AdaptLev.mem_intU.1 hx
  have hxf : x ∈ finU E a := (Subgroup.mem_inf.1 hxl).1
  have hcomp : ∀ u, Apart u w → cLoc u x = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxl).2 u) hu)
  have hK : (⟨x, hxf⟩ : finU E a) ∈ K₀ := by
    refine (mem_integral_iff _).2 fun u => ?_
    by_cases hu : Apart u w
    · show cLoc u x ∈ _
      rw [hcomp u hu]; exact one_mem _
    · exact hxi u hu
  by_contra hne
  have : (⟨x, hxf⟩ : finU E a) ∈ K₀ ∩ t S := ⟨hK, fun u hu => hcomp u (hS' u hu), hne⟩
  rw [hS] at this
  exact this

end GlobalTheory.Cong.AutFormFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopStep

theorem ext_mem_twisted_k1_level : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b →
    ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  intro E _ _ _ P hq N n hN r b c hn j h
  subst hN
  have hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b →
      ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E)) := by
    intro k hk a l ha hl
    have h0 : redP P (k.1 (Pi.single a 1) l) = 0 := by
      have := twTQ_HQ_entry hk ha hl
      rwa [redGL_val] at this
    exact intAt_div_of_redP hq (glint_entry k l a) h0
  refine mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_
  · intro x l
    rw [extI_val]
    by_cases hl : l.1 < n
    · rw [dif_pos (show l.1 < n + 1 - 1 by omega)]
      have := congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩
      exact this
    · rw [dif_neg (show ¬ l.1 < n + 1 - 1 by omega)]
      have e : l = Br.iL (rfl : n + 1 = n + 1) := Fin.ext (by have := l.2; show l.1 = n; omega)
      subst e
      rw [sumE_last, Units.val_one, one_mul]
  · exact fun a l ha hl => hent j h a l ha hl
  · intro a l ha hl
    have := hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl
    exact this

end GlobalTheory.TopStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClauseAtOfRepIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.GalCut

theorem clauseAt_of_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → UpperTheory.V.Af.RepIso r r' → ∀ c w, ClauseAt c π ι r w → ClauseAt c π ι r' w := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc
  obtain ⟨p, hp⟩ := hiso
  have hcw : ∀ {A : ValuationSubring Ω} (h : IsPlaceOver A w) (g : Weil h), p * r g = r' g * p :=
    fun h g => by rw [hp]; group
  have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
      p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
  cases c with
  | ss =>
    intro hl A h rc hrc σ hσ g
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h rc hrc σ hσ g
  | pure =>
    intro hl A h wt hwt
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h wt hwt
  | dR =>
    intro P AI hT A hA O _ _ _ Bw hj
    obtain ⟨h1, h2⟩ := hc P AI hT A hA O Bw hj
    obtain ⟨k1, -, -, k4⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact ⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩
  | crys =>
    intro P AI hT A hA O _ _ _ Bw hj σ hσ hS
    obtain ⟨-, k2, -, -⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact k2 (hc P AI hT A hA O Bw hj σ hσ hS)
  | iwa =>
    intro P AI hT A h O _ _ _ Bw hj σ hσ hI
    obtain ⟨h3, h4⟩ := hc P AI hT A h O Bw hj σ hσ hI
    exact ⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc =>
      (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩

end GlobalTheory.GalCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosedStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_subfields_compositum_closed : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  first | exact @GlobalTheory.CMSub.isCMField_sup_le_adjoin | exact GlobalTheory.CMSub.isCMField_sup_le_adjoin | (intros; apply GlobalTheory.CMSub.isCMField_sup_le_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satake_iff_localComponent_satake : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a) ≠ ⊥) := by
  first | (exact @GlobalTheory.Cong.satake_locComp) | (exact GlobalTheory.Cong.satake_locComp) | (intros; apply GlobalTheory.Cong.satake_locComp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satakeParameters_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' := by
  first | exact @GlobalTheory.AboveL.cg_hasSat_unique | exact GlobalTheory.AboveL.cg_hasSat_unique | (intros; apply GlobalTheory.AboveL.cg_hasSat_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

open GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem finPart_mem_integral_iff (k : finU E a) :
    finPart E a k ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isOpen_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w a : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  have h : IsOpen (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) : Set (GL (Fin a) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isOpen_KO
  rwa [hK] at h

theorem isClosed_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsClosed (GlobalTheory.LFun.KGL w a : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_KGL w a)

theorem mem_intU_iff_of_mem_locU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) :
    x ∈ intU a w ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w a :=
  ⟨fun h => (mem_intU.1 h).2 w (fun h' => h' rfl), mem_intU_of hx⟩

theorem isOpen_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  have e : (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) =
      (fun x : locU a w => cLoc w x.1) ⁻¹' (GlobalTheory.LFun.KGL w a : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_intU_iff_of_mem_locU x.2
  rw [e]
  exact (isOpen_KGL w a).preimage ((continuous_cLoc w).comp continuous_subtype_val)

theorem isCompact_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (intU a w : Set (UA E a)) := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) :=
    fun _ => Units.isEmbedding_embedProduct.t2Space
  let T : Set (finU E a) := {x | x.1 ∈ intU a w}
  have hK0 : IsCompact {x : finU E a | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} :=
    isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad)
  have hTsub : T ⊆ {x : finU E a | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} := by
    intro x hx
    have hx' := mem_intU.1 hx
    have hall : ∀ u, cLoc u x.1 ∈ GlobalTheory.LFun.KGL u a := by
      intro u
      by_cases hu : Apart u w
      · rw [((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 hx'.1).2 u hu]
        exact one_mem _
      · exact hx'.2 u hu
    refine ⟨finPart E a x, (finPart_mem_integral_iff x).2 hall, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  have hTe : T = (⋂ u, ⋂ (_ : Apart u w), {x : finU E a | cLoc u x.1 = 1}) ∩
      ⋂ u, ⋂ (_ : ¬ Apart u w), {x : finU E a | cLoc u x.1 ∈ GlobalTheory.LFun.KGL u a} := by
    ext x
    simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_intU,
      GlobalTheory.Cong.LevelExt.mem_locU_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨x.2, h.1⟩, h.2⟩⟩
  have hTc : IsClosed T := by
    rw [hTe]
    refine (isClosed_iInter fun u => isClosed_iInter fun _ => ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
    · exact (isClosed_KGL u a).preimage ((continuous_cLoc u).comp continuous_subtype_val)
  have hT := (hK0.of_isClosed_subset hTc hTsub).image continuous_subtype_val
  have e : Subtype.val '' T = (intU a w : Set (UA E a)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨⟨y, ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 (intU_le_locU w hy)).1⟩, hy, rfl⟩
  rwa [e] at hT

theorem intU_isCompact_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) :=
  fun _ _ _ _ _ w => ⟨isCompact_intU w, isOpen_intU w⟩

end GlobalTheory.Cong.AdaptLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorpStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  first | (exact @GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (exact GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (intros; apply GlobalTheory.Cong.cLoc_locU_bijective_open_continuous  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) → ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | exact GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | (intros; apply GlobalTheory.eventually_cofinite_under_of_eventually_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  first | exact @GlobalTheory.AbStep.exists_abelian_real_field | exact GlobalTheory.AbStep.exists_abelian_real_field | (intros; apply GlobalTheory.AbStep.exists_abelian_real_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRepStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
theorem _root_.GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  first | exact @GlobalTheory.Cong.exists_weight_of_isAutRepU | exact GlobalTheory.Cong.exists_weight_of_isAutRepU | (intros; apply GlobalTheory.Cong.exists_weight_of_isAutRepU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOverStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  first | exact @GlobalTheory.AboveL.exists_isPlaceOver_of_tower | exact GlobalTheory.AboveL.exists_isPlaceOver_of_tower | (intros; apply GlobalTheory.AboveL.exists_isPlaceOver_of_tower <;> assumption)
end

