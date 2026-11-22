import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

theorem codim_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) [FiniteDimensional L U] (anti : Antitone F) (hle : ∀ a, F a ≤ U)
    (exh : ∀ x ∈ U, ∃ a, x ∈ F a) (J : Multiset ℤ)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) (c : ℤ) :
    (finrank L U : ℤ) - finrank L (F c) = (Multiset.card (J.filter (· < c)) : ℤ) := by
  classical
  obtain ⟨s, hs⟩ : U.FG := Module.Finite.iff_fg.1 inferInstance
  have hm : ∀ x : s, ∃ a, (x : M) ∈ F a := fun x => exh x (hs ▸ Submodule.subset_span x.2)
  choose f hf using hm
  obtain ⟨b₁, hb₁⟩ := (Set.finite_range f).bddBelow
  obtain ⟨b₂, hb₂⟩ := J.toFinset.bddBelow
  have hb : F (min (min b₁ b₂) c) = U := by
    refine le_antisymm (hle _) ?_
    rw [← hs, Submodule.span_le]
    intro x hx
    exact anti ((min_le_left _ _).trans ((min_le_left _ _).trans (hb₁ ⟨⟨x, hx⟩, rfl⟩))) (hf ⟨x, hx⟩)
  have key : ∀ a, min (min b₁ b₂) c ≤ a →
      (finrank L U : ℤ) - finrank L (F a) = (Multiset.card (J.filter (· < a)) : ℤ) := by
    intro a ha
    induction a, ha using Int.le_induction with
    | base =>
      rw [hb, sub_self, Multiset.filter_eq_nil.2]
      · simp
      · intro u hu
        have : b₂ ≤ u := hb₂ (by simpa using hu)
        have h1 := min_le_left (min b₁ b₂) c
        have h2 := min_le_right b₁ b₂
        omega
    | succ a _ ih =>
      have h1 : J.filter (· < a + 1) = J.filter (· < a) + J.filter (a = ·) := by
        ext u
        simp only [Multiset.count_add, Multiset.count_filter]
        split_ifs <;> omega
      have h2 := h a
      rw [h1, Multiset.card_add, ← Multiset.count_eq_card_filter_eq]
      push_cast
      omega
  exact key c (min_le_right _ _)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}

omit [TopologicalSpace G] in

theorem codim_fil_zero {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K)
    [Module.Finite LL ↥(DdR PD ρ)] (U : ZMod n → Multiset ℤ) (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    (finrank LL ↥(DdR PD ρ) : ℤ) - finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  letI : Fintype (K →ₐ[Qp] LL) := Fintype.ofEquiv _ e
  have hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K := by
    rw [← Fintype.card_congr e, ZMod.card, hn]
  obtain ⟨h1, h2⟩ := GlobalTheory.DeRhamSplit.finrank_split PD hcard ρ
  rw [h1, h2 0, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI : FiniteDimensional LL ↥(DdRE PD ρ (e i)) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  exact codim_eq_card (FildR PD ρ (e i)) (DdRE PD ρ (e i))
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Cmp.SmallJumps.filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) (U i)
    (hU i (e i) (he i)) 0

variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]

omit [TopologicalSpace G] in

theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

theorem summand_of_crys [TopologicalSpace Qp] [TopologicalSpace LL] [CompactSpace G]
    (hO : GoodO (Qp := Qp) LL O) (hBK : Formalism.MainNotions.LocalSituation.bkADim PD) (hF : Formalism.MainNotions.LocalSituation.fontCore PD)
    {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K) (T : LocLat G Qp LL O)
    (hT : IsOpen (T.L.T : Set T.V)) (U : ZMod n → Multiset ℤ) (hU : CrysWith PD emb T.ρ U)
    {lam : O} (hlam : Irreducible lam)
    (h0 : (coefRep (latRep T.L) (O ⧸ Ideal.span {lam})).invariants = ⊥) (hfin : Module.Finite O (LatticeCohomology T.L)) :
    (∃ C : Submodule O (LatticeCohomology T.L), IsCompl (latticeFiniteCohomology PD T.L) C) ∧
      finrank O ↥(latticeFiniteCohomology PD T.L) = ∑ i, Multiset.card ((U i).filter (· < 0)) := by
  obtain ⟨_, _, _⟩ := hO.1
  refine ⟨exists_isCompl_of_saturated _ (h1fT_saturated PD T.L), ?_⟩
  let A : GRep G Qp LL O := { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hD, -⟩, hdR⟩ := hF LL O hO A
  haveI : Module.Finite LL ↥(DdR PD T.ρ) := hD
  have h1 : (finrank LL (FiniteCohomology PD T.ρ) : ℤ) = finrank LL ↥(H0V T.ρ) +
      ((finrank LL ↥(DdR PD T.ρ) : ℤ) - finrank LL ↥(DdR PD T.ρ ⊓ FilV PD (LL := LL) (V := T.V) 0)) :=
    hBK LL O hO A (hdR hU.1)
  rw [invariants_stableLattice_mod_irreducible_eq_bot T.L hlam h0, finrank_bot, codim_fil_zero PD emb hemb hK hn U hU.2, Nat.cast_zero,
    zero_add] at h1
  rw [finrank_h1fT PD T.L hT]
  exact_mod_cast h1

theorem summand_of_gal [TopologicalSpace Qp] [TopologicalSpace LL] [CompactSpace G]
    (hO : GoodO (Qp := Qp) LL O) (hBK : Formalism.MainNotions.LocalSituation.bkADim PD) (hF : Formalism.MainNotions.LocalSituation.fontCore PD)
    {n r : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (hn : n = finrank Qp K) (D : TopData n r)
    (Γ : GalData G Qp LL O) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V))
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g))
    (hU : CrysWith PD emb (twistRep Γ.T₀.ρ (chiLL LL Γ.χ₁⁻¹)) (fun i => (D.U i).map (· + -D.w i)))
    (hlam : Irreducible Γ.lam) (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥)
    (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    (∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C) ∧
      finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = D.dsum := by
  have h := summand_of_crys PD hO hBK hF emb hemb hK hn (twLat Γ.T₀ Γ.χ₁⁻¹ hχ) hT _ hU hlam
    (by
      change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
      rw [latRep_twLattice]
      exact h0) hfin
  refine ⟨h.1, h.2.trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

end General

open GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.TopSteps in

theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (S : TopSit P), Formalism.MainNotions.LocalSituation.bkADim (P.PD S.K) → Formalism.MainNotions.LocalSituation.fontCore (P.PD S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P AI _ S hBK hF hC hV hH
  obtain ⟨⟨-, hA, hn, hemb, -, hlam⟩, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have hO := (GlobalTheory.LocalIntegers.good_integers l S.LL).1
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  have h2 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1
  have hK : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) :=
    ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  exact summand_of_gal (P.PD S.K) hO hBK hF S.emb hemb hK hn S.D S.Γ (GlobalTheory.Cyc.locLat_isOpen hO S.Γ.T₀) h1.1 h2
    hlam hV.1 hH.1.2.1

end GlobalTheory.TopSteps.FinSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisDR

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (d : V ⊗[Qp] B) : d ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g d = d := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR_iff (d : V ⊗[Qp] BdR) : d ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g d = d := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem act_mul_ι (g : G) (c : K) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) (actVB PD ρ g d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [actVdR, mulVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι_mem (c : K) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d) ∈ DdR PD ρ := by
  rw [mem_DdR_iff]
  intro g
  rw [act_mul_ι, (mem_Dcris_iff PD ρ d).1 hd g]

theorem coord_mul_ι {I : Type} [DecidableEq I] (b : Basis I Qp V) (j : I) (c : K) (d : V ⊗[Qp] B) :
    equivFinsuppOfBasisLeft b
      (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) j =
      algebraMap K BdR c * PD.ι (equivFinsuppOfBasisLeft b d j) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, mul_add]
  | tmul v y =>
    have h : ∀ q : Qp, PD.ι (q • y) = q • PD.ι y := fun q =>
      (PD.ι.toLinearMap.restrictScalars Qp).map_smul q y
    simp [mulVdR, ιV, h]

theorem eq_zero_of_sum {m : ℕ} (x : Fin m → K)
    (hx : ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (d : Fin m → V ⊗[Qp] B)
    (h : ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) = 0)
    (i : Fin m) : d i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  refine hx (fun i => equivFinsuppOfBasisLeft b (d i) j) ?_ i
  have := congrArg (fun z => equivFinsuppOfBasisLeft b z j) h
  simp only [map_sum, Finsupp.finset_sum_apply, coord_mul_ι, map_zero, Finsupp.zero_apply] at this
  exact this

def cmpMap {m : ℕ} (x : Fin m → K) : (Fin m → ↥(Dcris PD ρ)) →ₗ[LL] ↥(DdR PD ρ) :=
  LinearMap.codRestrict (DdR PD ρ)
    (∑ i, (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i)) ∘ₗ (ιV PD (LL := LL) (V := V)) ∘ₗ
      (Dcris PD ρ).subtype ∘ₗ LinearMap.proj i)
    (fun d => by
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => mul_ι_mem PD ρ (x i) (d i).2)

theorem cmpMap_apply {m : ℕ} (x : Fin m → K) (d : Fin m → ↥(Dcris PD ρ)) :
    (cmpMap PD ρ x d : V ⊗[Qp] BdR) =
      ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) := by
  simp [cmpMap, LinearMap.sum_apply]

theorem abstract_cmp
    (hT : ∀ (m : ℕ) (x : Fin m → K), LinearIndependent K₀ x →
      ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (hfd : FiniteDimensional LL ↥(DdR PD ρ))
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V)
    (hc : IsCrys PD ρ) :
    finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V ∧
      ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i)) := by
  haveI := PD.finK
  haveI : FiniteDimensional K₀ K := Module.Finite.of_restrictScalars_finite Qp K₀ K
  let x := Module.finBasis K₀ K
  have hinj : Function.Injective (cmpMap PD ρ x) := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    funext i
    apply Subtype.ext
    refine eq_zero_of_sum PD (LL := LL) x (hT _ x x.linearIndependent) (fun i => (d i : V ⊗[Qp] B)) ?_ i
    rw [← cmpMap_apply, hd]
    rfl
  haveI hfdS : FiniteDimensional LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) :=
    FiniteDimensional.of_injective _ hinj
  have hpos : 0 < finrank K₀ K := finrank_pos
  haveI : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := LL) (φ := fun _ : Fin (finrank K₀ K) => ↥(Dcris PD ρ)) ⟨0, hpos⟩)
      (fun y => ⟨fun _ => y, rfl⟩)
  have hS : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold IsCrys at hc
    rw [hc, ← finrank_mul_finrank Qp K₀ K]
    ring
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (hS ▸ hge)
  refine ⟨heq, fun y hy => ?_⟩
  have hsurj : Function.Surjective (cmpMap PD ρ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hS.trans heq.symm)).1 hinj
  obtain ⟨d, hd⟩ := hsurj ⟨y, hy⟩
  refine ⟨_, x, fun i => d i, fun i => (d i).2, ?_⟩
  rw [← cmpMap_apply, hd]

end Abstract

theorem isDR_of_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ hc
  obtain ⟨hfd, hle⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  refine abstract_cmp (P.PD K) ρ (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hfd hle hc
  simpa only [P.PD_ι] using hb

end GlobalTheory.Per.CrisDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.JumpDual

def matG {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

theorem isDual1_dot {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ} (T U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (T g⁻¹).transpose) :
    IsDual1 PD (matRep T) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (T g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

theorem loc_cont (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    hM.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact h1.matrix_map hfc

theorem loc_dual (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw (rDuO D.nd i r x) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
        (Br.loc D.nbr i w hw (rTwO D.nd i r x) g⁻¹).transpose := by
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  rw [← GlobalTheory.CycBridge.locChi_epsU D i w hw g]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

theorem jump_dual : ∀ D : D7, DualJumpL D.loc → PotDRL D.loc → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ (x : ↥Xs) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) τ a ↔ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ (-a - 1) := by
  intro D hJ hP i r hr Xs w hw n hF x τ a
  obtain ⟨K', h, hN, hI, hS, Sig, Fr, -, -, -, -, hx⟩ := hF
  have hc := GlobalTheory.T.twisted_dual_families_continuous D i r hr x
  have cT := loc_cont D i w hw _ hc.1
  have cU := loc_cont D i w hw _ hc.2
  have hcr := (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hI hS _
    (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))).2.1 (hx x).1
  have hdR := hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) hcr
  exact hJ (D.nd.l i) (D.nbr i w hw).Kw (D.nbr i w hw).LL
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cU)
    (dotProductBilin _ _) (isDual1_dot _ _ _ (loc_dual D i w hw r x)) hdR τ a

end GlobalTheory.JumpDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisensteinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  first | exact @GlobalTheory.BSP.isUnit_toDisc_frobS_E | exact GlobalTheory.BSP.isUnit_toDisc_frobS_E | (intros; apply GlobalTheory.BSP.isUnit_toDisc_frobS_E <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBoundsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layer_DdR_bounds_alt : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ) (N : ℕ), (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → (∀ τ, ∀ n ∈ J τ, |n| ≤ N) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) := by
  first | exact @GlobalTheory.LayerJumps.layer_DdR_bounds | exact GlobalTheory.LayerJumps.layer_DdR_bounds | (intros; apply GlobalTheory.LayerJumps.layer_DdR_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOrderAboveLFiniteModulesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditionOrder_aboveL_finiteModules : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → LocSat bkP i s κ → LocCount bkP i s κ → LocCountFin bkP i s κ := by
  first | exact @GlobalTheory.LocCountFinite.locCountFin | exact GlobalTheory.LocCountFinite.locCountFin | (intros; apply GlobalTheory.LocCountFinite.locCountFin <;> assumption)
end

